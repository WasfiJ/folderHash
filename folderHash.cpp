// //////////////////////////////////////////////////////////
// folderHash.cpp
// Copyright (c) 2021 Wasfi JAOUAD. All rights reserved.
// v1.1 2021.03
// Verstaile CLI to the Portable Hashing Library by Stephan Brumme (all rights reserved).


#include <windows.h>
#include <strsafe.h>
#include "Shlwapi.h"

#include "crc32.h"
#include "md5.h"
#include "md5.h"
#include "sha1.h"
#include "sha256.h"
#include "keccak.h"
#include "sha3.h"
#include "xxhash64.h"

#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <atomic>
#include <chrono>
#include <algorithm>
#include <thread>

#define FH_VERSION "1.1"
using namespace std;

#define CLK chrono::high_resolution_clock
#define DURµs chrono::duration_cast<chrono::microseconds>
static CLK::time_point start = CLK::now();

size_t XXhashBytes = sizeof(uint64_t);
short xxW =  2*(short)XXhashBytes;
short crcW = 2*CRC32::HashBytes;
short md5W = 2*MD5::HashBytes;
short sha1W = 2*SHA1::HashBytes;
short sha2W = 2*SHA256::HashBytes;
short sha3W = 2*SHA3::Bits256/8;
short KeccakW = 2*Keccak::Keccak256/8;
short hashW = 0, hashNameW = 0;
const string crcN("CRC32"), xxN("XX"), md5N("MD5"), sha1N("SHA1"), sha2N("SHA2"), sha3N("SHA3"), KeccakN("Keccak");

short forwardSlash = 0;
inline void prHashLine(const string& algo, const short fszW, const size_t fSz, 
  const std::pair<string,size_t>&, const LPCSTR filename);
inline void fprHashLine(LPSTR& buffer, const string& algo, const size_t fSz, 
  const std::pair<string,size_t>&, const LPCSTR filename, short& c);

void usage();

// each cycle processes about 1 MByte (divisible by 144 => improves Keccak/SHA3 performance)
const size_t BufferSize = 144*7*4;

DWORD WINAPI processFiles(LPVOID p);
LPSTR* outT;
short processFile(size_t idx);
short process1File(LPSTR fn, LPCWSTR wfn, DWORD attr);
std::atomic<bool> stopProcessing(false);

size_t nbChunks, chunkSz, thMax = 2;
size_t minFilesChunk = 10, maxFilesChunk = 100;
UINT thIdx = 0;
HANDLE hMutex;
vector<bool> slots;
void runThreads();
UINT chewChunk(size_t chunk);
#define Lock() if (fileCnt>0 && WAIT_FAILED == WaitForSingleObject(hMutex, INFINITE)) {\
  printErr("Error: system failure (wait).", sysErr); return 60; }
#define unLock() if(fileCnt>0 && 0 == ReleaseMutex(hMutex)) { printErr("Error: system failure (release).", sysErr); return 62; }
#define sync(A) { Lock(); A; unLock(); }

inline void flushErr(LPCSTR format, ...);
inline void flushOut(LPCSTR format, ...);
inline char * wide2uf8(LPCWSTR);
inline wchar_t * uf8toWide(LPCCH);
#define nfree(A) free(A); A=nullptr;
#define sysErr 10000+GetLastError()
inline void printErr(LPCSTR msg, LONG errCode, int exitCode=0);
inline void  strCopy(LPSTR dst,  size_t sz, LPCSTR src, bool truncate=false);
inline void wstrCopy(LPWSTR dst, size_t sz, LPWSTR src, bool truncate=false);
inline void checkSnprintfA(HRESULT,size_t);
#define snprintfA(dst,sz,fmt,...) checkSnprintfA(StringCchPrintfA(dst,sz,fmt, ##__VA_ARGS__),sz)
inline void formatDur(__int64 dur, bool done = true);
template <typename T> void chkRealloc(T*& x, size_t count);
size_t folderIdx = 0, fileCnt = 0, hashedCnt = 0, totalSzHashed = 0, emptyDirsCnt = 0;
vector<size_t> fileIndxes;
struct dirCounts { size_t sz = 0, nbFiles = 0, nHidden = 0, nSys = 0; };
struct fsObj {
  LPSTR path, hsz = nullptr; 
  LPWSTR wpath;
  size_t sz, idx, parent, nbFiles, nHidden, nSys; 
  bool isdir = false, skip = false, hidden = false, system = false ;
};
vector<fsObj*> items;
size_t idx = -1;
dirCounts* travel(LPWSTR const & wpath, LPSTR const & path, size_t folderIdx, size_t& LargestFileSz);
short szWidth = 0;

inline void chkAlloc(size_t count) {};
template <typename T, class ... Ts> inline void chkAlloc(size_t count, T*& x, Ts&& ...args);
inline LPSTR  chkstrAlloc(size_t count,LPSTR& s){   chkAlloc(count, s); return s; };
inline LPWSTR chkwstrAlloc(size_t count,LPWSTR& s){ chkAlloc(count, s); return s; };

inline void chkVectResz(size_t count) {}
template <typename T, class ... Ts> inline void chkVectResz(size_t count, vector<T>& x, Ts&& ...args);

inline LPSTR catStr(std::initializer_list<LPCSTR> list);
inline LPWSTR catWstr(std::initializer_list<LPCWSTR> list);

LPSTR toupper(const string& s){
  string ret(s.size(), char());
  for(unsigned int i = 0; i < s.size(); ++i)
    ret[i] = (s[i] <= 'z' && s[i] >= 'a') ? s[i]-('a'-'A') : s[i];
  LPSTR a = nullptr; return (LPSTR) memcpy(chkstrAlloc(1+ret.size(),a), ret.c_str(), 1+ret.size());
}

inline short str2Sz(string& s, size_t& nbr){
  if(s.find_first_not_of(" 0123456789kKmMgG")!=string::npos){ 
    cerr << "\n  Error: not a supported file size designation: '"<<s<<"'"<<endl; return 3; }
  s.erase(std::remove(s.begin(), s.end(), ' '), s.end());
  if(s.find_first_not_of(" 0123456789")==string::npos){
    try{ nbr = ::stoll(s); } catch(logic_error){  // whatever
      cerr << "\n  Error: file size not a number: '"<<s<<"'"<<endl; return 3; }
  } else {
    string cs(s), chars = " 0123456789"; for(char c: chars) cs.erase(std::remove(cs.begin(), cs.end(), c), cs.end());
    if(cs.size()!=1){ cerr << "\n  Error: not a supported file size designation: '"<<s<<"'"<<endl; return 3; }
    for(char c: cs) s.erase(std::remove(s.begin(), s.end(), c), s.end());
    try{ nbr = ::stoll(s); } catch(logic_error){  // whatever
      cerr << "\n  Error: not a supported file size designation: '"<<s<<"'"<<endl; return 3; }
    switch(cs[0]){ case 'k': case'K': nbr *= 1024; break; case 'm': case'M': nbr *= 1024*1024; 
      break; case 'g': case'G': nbr *= 1024*1024*1024; break; }
  }
  return 0;
}

char * humanSize(size_t bytes){
  
  char *output; chkAlloc(32,output);
  if(bytes < 1024){ sprintf(output, "%zu bytes", bytes); return output; }
  
  char *suffix[] = {"bytes", "KB", "MB", "GB", "TB"};
  char length = sizeof(suffix) / sizeof(suffix[0]);

  int i = 0;
  double dblBytes = (double) bytes;

  if(bytes >= 1024) { 
    for (i = 0; (bytes / 1024) > 0 && i<length-1; i++, bytes /= 1024)
      dblBytes = bytes / 1024.0;
  }
  
  sprintf(output, "%.02lf %s", dblBytes, suffix[i]);
  return output;
}

bool userListFile = false, userOutFile = false, outFileAppend = false, allAlgos = false, computeXX = false, computeCrc32 = false;
bool computeMd5 = false, computeSha1 = false, computeSha2 = false, computeKeccak = false, computeSha3 = false, beQuiet = false;
bool showStats = false, showDur = false, listEmptyDirs = false, lowerCase = true, noFname = false, sizePrefix = true, filesByBlock = false;
bool algoPrefix = false, pretty = true, userSlash = false, baseNames = false, pathAsis = false, unixPath = false, cygPath = false;
bool noHidden = false, incPattrn = false, excPattern = false, szSmaller = false, szLarger = false, newerThan = false, olderThan = false;
bool cmpTime = false, userThreadCnt = false, IgnoreErr = true, delEmptyDirs = false, delEmptyFiles = false, delEmptyBoth = false;
bool listDirs = false, sysFiles = false, humanReadableSz = false, tagSysHidden = false;

bool algoPrefixU = false, filesByBlockU = false;

size_t leastSz = 0, mostSz = 0; size_t userThreadCntN = 0, max2List = 0, LargestFileSz2show = 0, nfiles2Show = 0;

void chunkLogic(){
  if(thMax == 1 || fileCnt <= thMax || fileCnt<=minFilesChunk){ chunkSz = fileCnt; nbChunks = thMax = 1; return; }
  chunkSz = fileCnt / thMax; 
  chunkSz = chunkSz>maxFilesChunk ? maxFilesChunk : chunkSz;
  chunkSz = chunkSz<minFilesChunk ? minFilesChunk : chunkSz;
  if(chunkSz >= fileCnt){ chunkSz = fileCnt; nbChunks = thMax = 1; return; }
  nbChunks = (-1+chunkSz+fileCnt) / chunkSz;
  if(nbChunks<=thMax) thMax = nbChunks;
  if(thMax==1) return;
  // distribute work load uniformly
  size_t uChunkSz = (-1+thMax+fileCnt) / thMax; if(uChunkSz>=nbChunks) return;
  if( uChunkSz < (8*minFilesChunk/10)){ thMax--; chunkLogic(); return; } //flushOut("\n#thMax = %lu\n", thMax); 
  else{ chunkSz = uChunkSz; nbChunks = (-1+chunkSz+fileCnt) / chunkSz; }
}

void usage(){
    cout <<"folderHash v"<<FH_VERSION<<" for Windows by Wasfi JAOUAD (c) 2021\n";
    cout <<"Versatile command-line interface to the Portable Hashing Library\n(https://create.stephan-brumme.com/hash-library/)\n\n";
    cout << " Usage:" << endl << endl;

    cout << "  folderHash [algos] [opts] file/folder                                     " << endl;
    cout << "  folderHash -h / --help : print this message                               " << endl << endl;

  //cout << " Ex.: folderHash -u -p *.jpg -crc -g -ss 0 -O \"2021.05.25 00:00:00\" c:/tmp" << endl << endl;
    cout << " Ex.: folderHash -u -crc -g -ss 0 -l 20k c:/tmp                             " << endl << endl;

    cout << "  Hash c:\\tmp, skip files less than 20 Kbytes in size (-l 20k), use upper- " << endl;
    cout << "  case (-u) for CRC32 hash (-crc), prefix each line with 'CRC32' (-g),      " << endl;
    cout << "  and do not show file sizes (-ss 0).                                       " << endl << endl;
  //cout << "  hash JPG files (-p) in c:\\tmp modified before April 5th, 2021 (-O). Use  " << endl;
  //cout << "  upper case (-u) for CRC32 hash (-crc), prefix each line with 'CRC32' (-g)," << endl;
  //cout << "                                         " << endl << endl;

    cout << " Output format: [algo] [file size] hash file_path                           " << endl << endl;

  //cout << " * Input/output (output is UTF-8)                                           " << endl;
  //cout << "     file / folder paths : must be last arguments                           " << endl;
  //cout << "     -i file : read 'file' for a list of files/folders to process           " << endl;
  //cout << "     -o file : write hashes to 'file' instead of standard output            " << endl;
  //cout << "     -append : append to output file instead of overwriting it              " << endl << endl;

    cout << "Available hash algorithms                                                   " << endl;
    cout << "   -a, --all : by default, overrides individual algorithm selections        " << endl;
    cout << "   -xx|-crc|-md5|-sha1|-sha2/sha256|-keccak|-sha3 : select one or more algos" << endl << endl;

    cout << "Available options:  [on] means the option is on by default                  " << endl;
    cout << "   To force an on/off option, use: -opt 0 / -opt 1                          " << endl;
    cout << "   Example: '-sd 0' will disable showing total run time                     " << endl << endl;

    cout << " * Display info                                                             " << endl;
    cout << "   -q,  --quiet, --silent : disable all info display, overrides other options" << endl;
    cout << "   -st, --stats    : show file/thread count info                            " << endl;
    cout << "   -sd, --duration : [on] show total run time                               " << endl;
    cout << "   -E,  --emptydirs: list empty folders encountered (in folder mode)        " << endl << endl;

    cout << " * Output formatting                                                        " << endl;
    cout << "   -u,  --uppercase  : use uppercase for hashes                             " << endl;
    cout << "   -ss, --size       : [on] prefix each line of output with file size       " << endl;
    cout << "   -hs, --human-size : show human-readable files sizes, not byte counts     " << endl;
    cout << "   -g : prefix each line of output with hash algorithm name                 " << endl;
    cout << "        This is on by default if multiple algos are to be used              " << endl;
    cout << "   -f,  --pretty     : [on] show formatted output (aligned columns)         " << endl;
    cout << "   -fb, --file-block : add an empty line after each file                    " << endl;
    cout << "       This is on by default if multiple algos are to be used               " << endl;
    cout << "   -ld, --list-dirs  : in folder mode, print each folder before its files   " << endl << endl;
    
    cout << "   File names/paths                                                         " << endl;
    cout << "   -nf, --no-fname : do not show file path/name, only the hash (file mode)  " << endl;
    cout << "   -sl, --my-slash : use my style (/ or \\) for paths. The first encountered" << endl;
    cout << "       forward or backword slash in provided file/folder name will be used. " << endl;
    cout << "   -sb, --basename : show file names, not full paths (overridden by -nf)    " << endl;
    cout << "   -su, --unix-path: show Unix-style paths (forward slash '/' separator)    " << endl;
    cout << "       Overrides -sl                                                        " << endl;
    cout << "   -pa, --path-asis: show provided path as it is, do not clean it up        " << endl;
    cout << "       This applies to provided path ; for subfolders, -sl & -su still apply" << endl << endl;
  //cout << "   -sc, --cyg-path : show Cygwin-style paths (/cygdrive/..)                 " << endl;

    cout << " * Filtering options                                                        " << endl;
    cout << "   -n, --at-most N  : stop after listing N files                            " << endl;
    cout << "   -s, --sys-files  : include system files/folders (not recommended)        " << endl;
    cout << "   -tg, --tag-hidden: prefix hidden/system files' paths/names with a '*'    " << endl;
    cout << "   -nh, --no-hidden : exclude hidden files/folders                          " << endl;
  //cout << "   -x pattern       : skip files matching 'pattern' (case insensitive)      " << endl;
  //cout << "      multiple patterns suported: -x *.txt -x \"a dir/\" ('a dir/' or       " << endl;
  //cout << "      'a dir\\') -> all text files and all files under 'a dir' folder       " << endl;
  //cout << "   -p pattern       : include matching files only (exclude all others)      " << endl;
    cout << "   -l, --smaller N  : process a file only if: size <= N bytes               " << endl;
    cout << "   -m, --larger N   : process a file only if: size >= N bytes               " << endl;
    cout << "       Nk/M/G: in kilo/mega/giga-bytes, ex: 23M = 23 x 1024 x 1024 bytes    " << endl;
  //cout << "   -N, --newer T    : process a file only if: timestamp >= T                " << endl;
  //cout << "   -O, --older T    : process a file only if: timestamp <= T                " << endl;
  //cout << "       T is a timestamp of format: 'YYYY.mm.dd HH:MM:SS', example:          " << endl;
  //cout << "       -n \"2021.04.25 18:10:23\" : newer than April 25th 2021, 18:10:23 PM " << endl;
  //cout << "   -T, --cmp-time A : file time attribute to consider for -n/-O options     " << endl;
  //cout << "       A can be: M or 'modification' (default), C or creation, A or access  " << endl << endl;
    cout << endl;
    cout << " * Operation                                                                " << endl;
    cout << "   -t N, --threads N : use N parallel threads at most. This will be reduced " << endl;
    cout << "       to the number of logical processors on your system if needed         " << endl;
    cout << "   -k, --keep-going       : [on] do not stop on error                       " << endl;
  //cout << "   -dd, --del-empty-dirs  : delete empty folders                            " << endl;
  //cout << "   -df, --del-empty-files : delete empty files                              " << endl;
  //cout << "   -de, --del-empty       : delete empty files and empty folders            " << endl << endl;
    cout << endl;
    cout << "  Last occurence of a repeated option overrides previous ones.              " << endl << endl;
  //cout << "  Last occurence of a repeated option overrides previous ones, except for -x" << endl;
  //cout << "  and -p which are exclusive.                                               " << endl;
  //cout << "  Number of threads is determined automatically, unless option -t is used.  " << endl << endl;
}

void seekHelp(short i){ cerr << "\n Type: 'folderHash -h' for usage information\n\n"; exit(i); }
void noArg(string opt,LPCSTR arg){
  cerr << "\n Error: missing argument to option '"<<opt<<"': "<<arg<<"\n\n"; seekHelp(4); }
void onOffarg(string& opt, bool& var, short& i, short& lastOptI){
  if(opt=="0"){ var = false; lastOptI = ++i; }
  if(opt=="1"){ var = true;  lastOptI = ++i; }
}

void listDir(size_t dirIdx, bool *folderDisp){
  size_t sz = items[dirIdx]->sz, nbFiles = items[dirIdx]->nbFiles;
  if(nullptr != folderDisp){ 
    if(folderDisp[dirIdx]) return;
    folderDisp[dirIdx] = true; 
    if(!showStats){ flushOut("%s:\n", items[dirIdx]->path); return; }
    if(humanReadableSz)
      flushOut("%s: %s, %zu file%s",         items[dirIdx]->path, humanSize(sz),   nbFiles, nbFiles==1?"":"s");
    else
      flushOut("%s: %zu byte%s, %zu file%s", items[dirIdx]->path, sz,sz==1?"":"s", nbFiles, nbFiles==1?"":"s");
  }
  else flushOut("%s, %zu files", humanSize(sz), nbFiles);
  size_t nHidden = items[dirIdx]->nHidden, nSys = items[dirIdx]->nSys;
  //flushOut("h=%zu, s=%zu\n", nHidden, nSys);
  if(!noHidden && nHidden==0 && sysFiles && nSys==0){ flushOut(" (no hidden/system files)\n"); return; }
  if(noHidden && !sysFiles){ flushOut("\n"); return; }

  if(!noHidden){ if(nHidden>0)     flushOut(" (%zu hidden", nHidden);
                 else              flushOut(" (%s hidden", nbFiles==1?"not":"none are"); }
  if(sysFiles){
    if(nSys>0) flushOut(", %zu system file%s)\n", nSys, nSys==1?"":"s");
    else{ 
      if(!noHidden) flushOut(", no system files)\n");
      else flushOut(" (no system files)\n");
    }
  }
  else flushOut(")\n"); 
}

int main(int argc, char** argv) {

  setlocale ( LC_ALL, "en-US.65001" );
  int nbArgs;
  auto arglist = CommandLineToArgvW(GetCommandLineW(), &nbArgs);
  if(arglist==nullptr) printErr(nullptr, sysErr, 21);

  // syntax check
  if(argc == 1) { cerr << endl << "  Error: no file/folder argument provided. Hash what ? " << endl;
    usage(); return 1; }
  if(argc==2){ string opt1(argv[1]); if(opt1=="-h" || opt1=="-help"){ usage(); return 0; }}
  
  short multiAlgos = -1, lastOptI = 0, unkwnOpt = 0; vector<short> notOpt;
  for(short i=1; i<argc; i++){   string opt = argv[i];
    if(opt=="-h" || opt=="--help"){ cerr << "\n  option #"<<i<<" : "<<opt<<endl; usage(); return 0; }
    if(opt=="-o"){ userOutFile = true; lastOptI = i; continue; }
    if(opt=="-append"){ outFileAppend = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),outFileAppend,i,lastOptI); continue; }
    if(opt=="-a"||opt=="--all"||opt=="-A"){ allAlgos = true; multiAlgos++; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),allAlgos,i,lastOptI); continue; }
    if(opt=="-xx"||opt=="-XX"||opt=="xx"||opt=="XX"){ computeXX = true; lastOptI = i; multiAlgos++; continue; }
    if(opt=="-crc"||opt=="-crc32"||opt=="CRC"||opt=="CRC32"){ computeCrc32 = true; lastOptI = i; multiAlgos++; continue; }
    if(opt=="-md5"||opt=="-MD5"||opt=="md5"||opt=="MD5"){ computeMd5 = true; lastOptI = i; multiAlgos++; continue; }
    if(opt=="-sha1"||opt=="-SHA1"||opt=="sha1"||opt=="SAH1"){ computeSha1 = true; lastOptI = i; multiAlgos++; continue; }
    if(opt=="-sha2"||opt=="-sha256"||opt=="-SAH2"||opt=="-SHA256"||opt=="SAH2"||opt=="sha2"||opt=="sha256"||opt=="SHA256"){ 
      computeSha2 = true; lastOptI = i; multiAlgos++; continue; }
    if(opt=="-keccak"){ computeKeccak = true; lastOptI = i; multiAlgos++; continue; }
    if(opt=="-sha3"||opt=="-SHA3"||opt=="sha3"||opt=="SHA3"){ computeSha3 = true; lastOptI = i; multiAlgos++; continue; }
    if(opt=="-q"||opt=="--quiet"||opt=="--silent"){ beQuiet = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),beQuiet,i,lastOptI); continue; }
    if(opt=="-st"||opt=="--stats"){ showStats = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),showStats,i,lastOptI); continue; }
    if(opt=="-sd"||opt=="--duration"){ showDur = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),showDur,i,lastOptI); continue; }
    if(opt=="-E"||opt=="--emptydirs"){ listEmptyDirs = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),listEmptyDirs,i,lastOptI); continue; }
    if(opt=="-u"||opt=="--uppercase"){ lowerCase = false; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),lowerCase,i,lastOptI); continue; }
    if(opt=="-ld"||opt=="--list-dirs"){ listDirs = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),listDirs,i,lastOptI); continue; }
    if(opt=="-nf"||opt=="--no-fname"){ noFname = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),noFname,i,lastOptI); continue; }
    if(opt=="-ss"||opt=="--size"){ sizePrefix = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),sizePrefix,i,lastOptI); continue; }
    if(opt=="-hs"||opt=="--human-size"){ humanReadableSz = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),humanReadableSz,i,lastOptI); continue; }
    if(opt=="-g"){ algoPrefix = algoPrefixU = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),algoPrefix,i,lastOptI); continue; }
    if(opt=="-f"||opt=="--pretty"){ pretty = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),pretty,i,lastOptI); continue; }
    if(opt=="-fb"||opt=="--file-block"){ filesByBlock = filesByBlockU = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),filesByBlock,i,lastOptI); continue; }
    if(opt=="-sl"||opt=="--my-slash"){ userSlash = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),userSlash,i,lastOptI); continue; }
    if(opt=="-sb"||opt=="--basename"){ baseNames = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),baseNames,i,lastOptI); continue; }
    if(opt=="-su"||opt=="--unix-path"){ unixPath = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),unixPath,i,lastOptI); continue; }
    if(opt=="-su"||opt=="--unix-path"){ unixPath = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),unixPath,i,lastOptI); continue; }
    if(opt=="-pa"||opt=="--path-asis"){ pathAsis = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),pathAsis,i,lastOptI); continue; }
    if(opt=="-sc"||opt=="--cyg-path"){ cygPath = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),cygPath,i,lastOptI); continue; }
    if(opt=="-n"||opt=="--at-most"){
      if(i==argc-1) noArg(opt,"maximum count of files to list");  
      if(argv[i+1][0]=='-' || (max2List = strtoul(argv[i+1],nullptr,0))==0){ 
        cerr << "\n Error: expecting a positive number after option '"<<opt<<"', not '"<<argv[i+1]<<"'\n" ; seekHelp(3); }
      if(errno==ERANGE){ cerr << "\n Error: "<<opt<<": maximum count of files to list: "<<argv[i+1]<<": "; perror(""); seekHelp(3); }
      lastOptI = ++i; continue; }
    if(opt=="-s"||opt=="--sys-files"){ sysFiles = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),sysFiles,i,lastOptI); continue; }
      if(opt=="-tg"||opt=="--tag-hidden"){ tagSysHidden = true; lastOptI = i;
        if((i+1)<argc) onOffarg(string(argv[i+1]),tagSysHidden,i,lastOptI); continue; }
    if(opt=="-nh"||opt=="--no-hidden"){ noHidden = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),noHidden,i,lastOptI); continue; }
    if(opt=="-x"){ incPattrn = true; continue; }
    if(opt=="-p"){ excPattern = true; continue; }
    if(opt=="-l"||opt=="--smaller"){ szSmaller = true; lastOptI = i;
      if(i==argc-1) noArg(opt,"file size");
      if(argv[i+1][0]=='-'){ cerr << "\n Error: expecting a positive number after option '"<<opt<<"'\n"; seekHelp(3); }
      if(0!=str2Sz(string(argv[i+1]), mostSz)) seekHelp(3);
      lastOptI = ++i; continue; }
    if(opt=="-m"||opt=="--larger"){ szLarger = true; lastOptI = i;
      if(i==argc-1) noArg(opt,"file size");
      if(argv[i+1][0]=='-'){ cerr << "\n Error: expecting a positive number after option '"<<opt<<"'\n"; seekHelp(3); }
      if(0!=str2Sz(string(argv[i+1]), leastSz)) seekHelp(3);
      lastOptI = ++i; continue; }
    if(opt=="-N"||opt=="--newer"){ newerThan = true; lastOptI = i; continue; }
    if(opt=="-O"||opt=="--older"){ olderThan = true; lastOptI = i; continue; }
    if(opt=="-T"||opt=="--cmp-time"){ cmpTime = true; lastOptI = i; continue; }
    if(opt=="-t"||opt=="--threads"){ userThreadCnt = true; 
      if(i==argc-1) noArg(opt,"thread count");  
      if(argv[i+1][0]=='-' || (userThreadCntN = strtoul(argv[i+1],nullptr,0))==0){ 
        cerr << "\n Error: expecting a positive number after option '"<<opt<<"', not '"<<argv[i+1]<<"'\n" ; seekHelp(3); }
      if(errno==ERANGE){ cerr << "\n Error: "<<opt<<": maximum number of threads: "<<argv[i+1]<<": "; perror(""); seekHelp(3); }
      lastOptI = ++i; continue; }
    if(opt=="-k"||opt=="--keep-going"){ IgnoreErr = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),IgnoreErr,i,lastOptI); continue; }
    if(opt=="-dd"||opt=="--del-empty-dirs"){ delEmptyDirs = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),delEmptyDirs,i,lastOptI); continue; }
    if(opt=="-df"||opt=="--del-empty-files"){ delEmptyFiles = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),delEmptyFiles,i,lastOptI); continue; }
    if(opt=="-de"||opt=="--del-empty"){ delEmptyBoth = true; lastOptI = i;
      if((i+1)<argc) onOffarg(string(argv[i+1]),delEmptyBoth,i,lastOptI); continue; }
    if(i<argc-1) {
      cerr << "\n  Error: unrecognized option: " << opt; unkwnOpt++; }
  }
  if(unkwnOpt){ cerr << "\n"; seekHelp(3); }
  if(lastOptI==argc-1) { cerr << endl << "  Error: no file/folder argument provided. Hash what ? " << endl;
    seekHelp(1); }
  
  if(multiAlgos>0 || 
     !(allAlgos || computeXX || computeCrc32 || computeKeccak || computeMd5 || computeSha1 || computeSha2 || computeSha3)) {
     if(!algoPrefixU) algoPrefix = true; if(!filesByBlockU) filesByBlock = true; }
  if(allAlgos || 
     !(computeXX || computeCrc32 || computeKeccak || computeMd5 || computeSha1 || computeSha2 || computeSha3)) {
     computeXX = computeCrc32 = computeKeccak = computeMd5 = computeSha1 = computeSha2 = computeSha3 = true;
     if(!algoPrefixU) algoPrefix = true; if(!filesByBlockU) filesByBlock = true;; }

  if(beQuiet) showDur = showStats = filesByBlock = 0;
  
  hashNameW = std::max<short>({computeXX?(short)xxN.size():0, computeCrc32?(short)crcN.size():0, computeMd5?(short)md5N.size():0,
    computeSha1?(short)sha1N.size():0, computeSha2?(short)sha2N.size():0, computeSha3?(short)sha3N.size():0, 
    computeKeccak?(short)KeccakN.size():0});

  hashW = std::max<short>({computeXX?xxW:0, computeCrc32?crcW:0, computeMd5?md5W:0, computeSha1?sha1W:0,
    computeSha2?sha2W:0, computeSha3?sha3W:0, computeKeccak?KeccakW:0});
  
  // path valid ?
  LPWSTR pathW = arglist[nbArgs-1];
  LPSTR path = argv[argc-1];  

  LPWSTR fpath;  chkAlloc(32768,fpath);
  auto m = strncmp(path,"\\\\?\\",4);
  { WCHAR *slash = pathW;
    while(nullptr != (slash = wcsstr(slash, L"/"))) *slash = L'\\';

    DWORD plen; LPWSTR tmp = nullptr; HANDLE f;    
    #define OPEN_FILE GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, 0,                          nullptr
    #define OPEN_DIR  GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, FILE_FLAG_BACKUP_SEMANTICS, nullptr
    if(m==0) f = (INVALID_HANDLE_VALUE == (f = CreateFileW(pathW, OPEN_DIR))) ? CreateFileW(pathW, OPEN_FILE) : f;
    else { tmp = catWstr({ L"\\\\?\\",pathW }); f = CreateFileW(tmp, OPEN_DIR); nfree(tmp); f = (f==INVALID_HANDLE_VALUE) ?
      CreateFileW(tmp = catWstr({ L"\\\\?\\",pathW }), OPEN_FILE) : f; nfree(tmp); }
    if(f==INVALID_HANDLE_VALUE) printErr(catStr({"Error opening: ",path}),sysErr,7);
    
    DWORD maxPath = 2<<15;
    typedef DWORD (WINAPI* pfGetFinalPath)(HANDLE, LPWSTR, DWORD, DWORD);
    pfGetFinalPath gfpbh = (pfGetFinalPath) GetProcAddress(GetModuleHandleA("kernel32"), "GetFinalPathNameByHandleW");
    if(gfpbh){ plen = gfpbh(f,fpath, maxPath*sizeof(WCHAR),0);
      if(0==plen) printErr(catStr({"Error: GetFinalPathNameByHandleW(): ",path}), sysErr, 8);
      if(maxPath<1+plen){ flushErr("\n  Error: path too long: %-100.100s..\n\n", path); return 9; }
    }
    else {
      if(m==0) plen = GetFullPathNameW(pathW, maxPath*sizeof(WCHAR),fpath,nullptr);
      else{ plen = GetFullPathNameW(tmp = catWstr({L"\\\\?\\",pathW}), maxPath,fpath,nullptr); nfree(tmp); }
      if(0==plen) printErr(catStr({"\n Error: GetFullPathNameW(): ",path}), sysErr, 77);
      if(maxPath<1+plen){ flushErr("\n  Error: path too long: %-100.100s..\n\n", path); return 78; }
    }
    CloseHandle(f);
  }
  LocalFree(arglist);

  DWORD attr = GetFileAttributesW(fpath);
  if(attr==INVALID_FILE_ATTRIBUTES) printErr(path, sysErr, 22);
  
  if(pathAsis){
    size_t n = strlen(path)-1; if(path[n]=='\\' || path[n]=='/') path[n] = '\0';
  } 
  else
    if(nullptr==memmove(path = wide2uf8(fpath),path+4,strlen(path))) return 1;
  
  if(unixPath || userSlash) {    
    if(!unixPath && userSlash) {
      char *slash = strstr(argv[argc-1],"/"), *bslash = strstr(argv[argc-1],"\\");
           if(nullptr==slash && bslash==nullptr) forwardSlash = 0;
      else if(nullptr!=slash && bslash==nullptr) forwardSlash = 1;
      else if(nullptr==slash && bslash!=nullptr) forwardSlash = 0;
      else if(slash<bslash) forwardSlash = 1;
      else if(bslash<slash) forwardSlash = 0;
    } 
    if(unixPath) forwardSlash = 1;
    
    CHAR *bslash = path;
    if(!pathAsis && forwardSlash==1) while(nullptr!=(bslash = strstr(bslash,"\\"))) *bslash = '/';
  }

  size_t LargestFileSz = 0; 
  if(attr&FILE_ATTRIBUTE_DIRECTORY){
    dirCounts *dummy = travel(fpath, path, -1, LargestFileSz); free(dummy);
    items[0]->hidden = attr&FILE_ATTRIBUTE_HIDDEN; items[0]->system = attr&FILE_ATTRIBUTE_SYSTEM;
  }
  else { if(showStats) flushErr("\n"); CLK::time_point lStart = CLK::now();
    process1File(path,fpath,attr); 
    long long dur = DURµs( CLK::now() - start).count();
    if(showStats){ flushErr("\nHashed %zu bytes",totalSzHashed);
    if(totalSzHashed>=1024) flushErr(" (%s), average data rate: %s/s\n", 
        humanSize(totalSzHashed), humanSize(1000000*totalSzHashed/dur));
      else flushErr("\n"); }
    if(showDur) formatDur(dur); return 0; 
  }
  
  if(fileCnt==0){
    if(showStats) flushErr("\n#Files = 0\n");
    if(listEmptyDirs){ flushOut("\n");
      flushOut("%zu empty folder%s: \n", emptyDirsCnt, emptyDirsCnt==1? "":"s");
      for(auto fo: items) if(fo->isdir && fo->sz==0) flushOut("  %s\n", fo->path);
    }
    if(showStats) flushErr("\nHashed 0 bytes. Folder size: %s.\n", humanSize(items[0]->sz));
    else if(listEmptyDirs) flushErr("\n");
    if(showDur) formatDur( DURµs(CLK::now() - start).count() );
    
    return 0;
  }

  if(!humanReadableSz) szWidth = (short) ::to_string(LargestFileSz2show).length();
   
  
  SYSTEM_INFO *sysInfo; chkAlloc(1,sysInfo); GetSystemInfo(&*sysInfo); thMax = sysInfo->dwNumberOfProcessors; free(sysInfo);
  if(userThreadCnt && userThreadCntN<=thMax) thMax = userThreadCntN;
  if(thMax<2 && userThreadCntN!=1) thMax = 2;
  if(max2List>0) fileCnt = max2List;
  chunkLogic();
  if(showStats){ flushErr("\n#Files = %lu\n", fileCnt);
    if(thMax>1) flushErr("  Processing files by packs of %zu (%zu packs)\n  Using %zu workers\n", chunkSz, nbChunks, thMax);
  }

  size_t mis = 0, totalMiss = 0, totalNoFile = 0;
  slots = vector<bool>(nbChunks, false);
  chkAlloc(fileCnt,outT);
  CLK::time_point lStart = CLK::now();
  runThreads();
  CLK::time_point lEnd = CLK::now();
  listEmptyDirs = listEmptyDirs && emptyDirsCnt>0;
  filesByBlock = filesByBlock && hashedCnt>1;
  if(showDur || showStats || filesByBlock || listEmptyDirs) flushErr("\n");
  LPCSTR fBlock = filesByBlock ? "\n":"";
  if(max2List==0) max2List = hashedCnt;
  size_t i, dirIdx, j = 0; bool *folderDisp; chkAlloc(items.size(),folderDisp);
  for(i=0;i<fileCnt;i++) if(nullptr!=outT[i]) { 
    if(listDirs) listDir(dirIdx = items[fileIndxes[i]]->parent, folderDisp);
    flushOut("%s%s\n",outT[i],fBlock); delete[] outT[i]; if(++j==(max2List-1)) break;
  }
  for(size_t k=i+1;k<fileCnt;k++) if(nullptr!=outT[k]) { 
    if(listDirs) listDir(dirIdx = items[fileIndxes[k]]->parent, folderDisp);
    flushOut("%s%s",outT[k],fBlock); flushErr("\n"); delete[] outT[k]; break;
  }
  fileIndxes = vector<size_t>(); slots = vector<bool>(); delete[] outT;
  
  if(listEmptyDirs){ if(!filesByBlock) flushOut("\n");
    flushOut("%zu empty folder%s: \n", emptyDirsCnt, emptyDirsCnt==1? "":"s");
    for(auto fo: items) if(fo->isdir && fo->sz==0) flushOut("  %s\n", fo->path);
  }

  if(showDur || showStats){ if(listEmptyDirs || !filesByBlock) flushErr("\n"); }
  else if(listEmptyDirs) flushErr("\n");
  
  if(showStats){ long long dur = DURµs(lEnd - lStart).count();
    flushErr("Hashed %zu bytes (%s) in ", totalSzHashed, humanSize(totalSzHashed)); formatDur(dur,false);
    //if(hashedCnt!=fileCnt) 
    flushErr(". Processed %zu file%s. Average data rate: %s/s\n", hashedCnt, hashedCnt==1?"":"s", 
      humanSize(1000000*totalSzHashed/dur));
    flushErr("Folder size: "); listDir(0,nullptr);
  }

  //_sleep(1000);
  if(showDur) formatDur( DURµs(CLK::now() - start).count() );

  return 0;
}

void runThreads(){
  
  HANDLE* hThread = nullptr; chkAlloc(thMax, hThread); 
  hMutex = CreateMutex(nullptr, FALSE, nullptr);
  if(nullptr == hMutex) printErr("Error: could not create mutex.", sysErr, 61);
  vector<DWORD> dwThreadId, dwExitCode;
  chkVectResz(thMax, dwThreadId, dwExitCode);

  size_t p;
  for(p=0; p<thMax; p++) { 
    hThread[p] = CreateThread(nullptr, 0, processFiles, nullptr, 0, &dwThreadId[p]);
    if (nullptr == hThread[p]) printErr("Error: failed to create thread.", sysErr, 59);
  }
  if (WAIT_FAILED==WaitForMultipleObjects((DWORD)thMax, hThread, TRUE, INFINITE)) 
    printErr("Error: system failure (wait multi).", sysErr, 60);

  for(p=0; p<thMax; p++) { GetExitCodeThread(hThread[p], &dwExitCode[p]);  CloseHandle(hThread[p]); }

}

dirCounts* travel(LPWSTR const & wpath, LPSTR const & path, size_t parentIdx, size_t& LargestFileSz) {

  //flushOut(" wPath_ = .%s.\n", wide2uf8(wpath));
  size_t folderIdx = 0, sz; fsObj *fo; dirCounts *dc; 
  chkAlloc(1, dc); dc->sz = dc->nbFiles = 0;
  chkAlloc(1, fo);
  chkAlloc(sz = 1+strlen(path),  fo->path);   strCopy(fo->path,  sz, path);
  chkAlloc(sz = 1+wcslen(wpath), fo->wpath); wstrCopy(fo->wpath, sz, wpath);
  fo->nbFiles = fo->sz = fo->nHidden = fo->nSys = 0; fo->isdir = true; fo->parent = parentIdx; 
  fo->idx = folderIdx = ++idx; items.push_back(fo);
  
  WIN32_FIND_DATA wfd; WCHAR * tmp;
  HANDLE hFind = FindFirstFileW(tmp = catWstr({wpath,L"\\*"}), &wfd); auto err = GetLastError();
  if(INVALID_HANDLE_VALUE == hFind) printErr(catStr({"Error: FindFirstFileW(): ",wide2uf8(wpath)}), 10000+err, 52);
  free(tmp);
  if(ERROR_FILE_NOT_FOUND == err) return dc;
  
  size_t folderSz = 0, nbFiles = 0, hiddenCnt = 0, sysCnt = 0; LPSTR fn, catp; LPWSTR wcatp; bool b, hidden, system;
  vector<shared_ptr<WCHAR>> wdirs; vector<shared_ptr<CHAR>> dirs; vector<bool> vhidden;  vector<bool> vsystem;
  do { 
    if(!lstrcmpW(wfd.cFileName, L".") || !lstrcmpW(wfd.cFileName, L"..") || 
       wcsstr(wfd.cFileName, L"\\$RECYCLE.BIN") ||
       wcsstr(wfd.cFileName, L"System Volume Information")) continue;
    
    unique_ptr<CHAR> q( fn = wide2uf8(wfd.cFileName));
    shared_ptr<CHAR> p( catp = catStr({path,forwardSlash==1?"/":"\\",fn}) );
    shared_ptr<WCHAR> wp( wcatp = catWstr({wpath,L"\\",wfd.cFileName}) );
    sz = 2+strlen(fn)+strlen(path);

    hidden = wfd.dwFileAttributes&FILE_ATTRIBUTE_HIDDEN;
    system = wfd.dwFileAttributes&FILE_ATTRIBUTE_SYSTEM;
    if((noHidden && hidden) || (!sysFiles && system)) continue;
    
    if(wfd.dwFileAttributes&FILE_ATTRIBUTE_DIRECTORY){ wdirs.push_back(wp); dirs.push_back(p); 
      vhidden.push_back(hidden); vsystem.push_back(system); continue; }
    
    fsObj *fo; chkAlloc(1, fo);
    chkAlloc(sz, fo->path); strCopy(fo->path, sz, catp);
    chkAlloc(sz = 1+wcslen(wcatp), fo->wpath); wstrCopy(fo->wpath, sz, wcatp);
    fo->parent = folderIdx; fo->idx = ++idx; fo->isdir = false; fo->nbFiles = 0;
    fo->sz = sz = wfd.nFileSizeHigh * 0x100000000 + wfd.nFileSizeLow;  // stupid warning C4307 on their own formula
    //sz = fo->sz = wfd.nFileSizeHigh * (MAXDWORD+1) + wfd.nFileSizeLow;
    
    b = false;
    if(hidden){ hiddenCnt++; fo->hidden = true; if(noHidden) b = fo->skip = true; }
    if(system){ sysCnt++; fo->system = true; if(!b && !sysFiles) b = fo->skip = true; }
    if(!b && max2List>0 && ++nfiles2Show>max2List) b = fo->skip = true;
    if(!b){
      if(humanReadableSz){ short n = (short)strlen(fo->hsz = humanSize(sz)); szWidth = szWidth<n ? n:szWidth; }
      else LargestFileSz2show = LargestFileSz2show<sz ? sz:LargestFileSz2show;
    }
    
    items.push_back(fo);fileIndxes.push_back(idx); ++fileCnt;
    folderSz += sz; nbFiles++; LargestFileSz = LargestFileSz<sz ? sz : LargestFileSz;

  } while(FindNextFileW(hFind, &wfd));
  if(ERROR_NO_MORE_FILES!=GetLastError()) printErr(catStr({"Error: FindNextFileW(): ",wide2uf8(wpath)}), sysErr, 53);
  FindClose(hFind);

  dirCounts *d; size_t i = 0;
  for(auto wdir : wdirs) { 
    d = travel(wdir.get(), dirs[i++].get(),folderIdx,LargestFileSz);
    items[folderIdx]->hidden = vhidden[i]; items[folderIdx]->system = vsystem[i]; 
    hiddenCnt += d->nHidden; sysCnt += d->nSys; folderSz += d->sz; nbFiles += d->nbFiles; delete[] d;    
  }

  items[folderIdx]->sz = dc->sz = folderSz; items[folderIdx]->nbFiles = dc->nbFiles = nbFiles;
  items[folderIdx]->nHidden = dc->nHidden = hiddenCnt; items[folderIdx]->nSys = dc->nSys = sysCnt; if(folderSz==0) emptyDirsCnt++;
  return dc;
}

DWORD WINAPI processFiles(LPVOID p) {
  //UINT thId = 0;
  size_t k; bool gotSlot;

  while(!stopProcessing) {  // while there are chunks to consume
    gotSlot = false;
    Lock();
      for (k = 0; k < nbChunks; k++)
        if (!slots[k]){ slots[k] = gotSlot = true; break; }  // slot/chunk k is taken now
      //if (thId == 0) thId = ++thIdx; 
    unLock(); 
    if (!gotSlot) return 0; // no-mo-chunks

    if(chewChunk(k+1)!=0 && !IgnoreErr){ stopProcessing = true; return 1; }
    
  }
  return 0;
}

UINT chewChunk(size_t chunk){
  size_t s = chunkSz*(chunk-1), deleted = 0;
  auto e = s -1+chunkSz; if(e>=fileCnt) e = fileCnt - 1;
  size_t mis = 0;
  //Lock(); flushOut(" %d: chunk %zu %zu, %d\n", thIdx, s, e, outLn[thIdx-1]); unLock();
  for(size_t i=s; i<=e; i++){ if(stopProcessing) return 0;
    if(0!=processFile(i)){ mis++; if(!IgnoreErr){ stopProcessing=true; return 1; }}
  }
  return 0;
}

short processFile(size_t fidx) {
  
  if(items[fileIndxes[fidx]]->skip) return 0;
  if(max2List>0) { bool stop = false;
    if(thMax>1) sync( if(hashedCnt+1>max2List) stop = true; )
    else if(hashedCnt+1>max2List) stop = true;
    if(stop) return 0; }

  size_t sz = items[fileIndxes[fidx]]->sz;  
  LPSTR p; LPCSTR fn = items[fileIndxes[fidx]]->path;

  XXHash64 xxhash(0); CRC32 dCrc32; MD5 dMd5; SHA1 dSha1; SHA256 dSha2;       
  Keccak dKeccak(Keccak::Keccak256); SHA3 dSha3(SHA3::Bits256);
  
  char *buffer; chkAlloc(BufferSize, buffer); 
  
  auto f = CreateFileW(items[fileIndxes[fidx]]->wpath, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, 0, nullptr);
  if(f==INVALID_HANDLE_VALUE){ printErr(p=catStr({"  Error opening file: ",fn,"\n"}),sysErr,0); free(p); 
    if(!IgnoreErr) stopProcessing=true; return 1; }
  
  DWORD nBytesRead;
  while (ReadFile(f, buffer, (DWORD) BufferSize, &nBytesRead, NULL) && nBytesRead){

    if (computeCrc32)  dCrc32 .add(buffer, nBytesRead);
    if (computeMd5)    dMd5   .add(buffer, nBytesRead);
    if (computeSha1)   dSha1  .add(buffer, nBytesRead);
    if (computeSha2)   dSha2  .add(buffer, nBytesRead);
    if (computeXX)     xxhash .add(buffer, nBytesRead); 
    if (computeKeccak) dKeccak.add(buffer, nBytesRead);
    if (computeSha3)   dSha3  .add(buffer, nBytesRead);

  }; auto Err = GetLastError(); CloseHandle(f);
  if(Err){ printErr(p=catStr({"  Error reading file: ",fn,"\n"}),10000+Err,0); free(p); if(!IgnoreErr) stopProcessing=true; return 1; }

  chkRealloc(buffer,1); *buffer = 0;
  short c = 0;

  // show results
  LPSTR fname;
  if(tagSysHidden && ( (!noHidden && items[fileIndxes[fidx]]->hidden) || (sysFiles && items[fileIndxes[fidx]]->system) ) ) 
    fname = catStr({"*",fn});
  else fname = catStr({fn});
  if(!noFname && baseNames){ char *slash = strrchr(fname,'/'), *bslash = strrchr(fname,'\\');
    if(slash!=nullptr) memmove(fname,slash+1,strlen(fname));
    else if(bslash!=nullptr) memmove(fname,bslash+1,strlen(fname));
  }
  #define P std::make_pair<string,size_t>
  if(computeCrc32)  fprHashLine(buffer, crcN,    humanReadableSz? fidx:sz, P(dCrc32.getHash(),0),  fname, c);
  if(computeXX)     fprHashLine(buffer, xxN,     humanReadableSz? fidx:sz, P("",xxhash.hash()),    fname, c);
  if(computeMd5)    fprHashLine(buffer, md5N,    humanReadableSz? fidx:sz, P(dMd5.getHash(),0),    fname, c);
  if(computeSha1)   fprHashLine(buffer, sha1N,   humanReadableSz? fidx:sz, P(dSha1.getHash(),0),   fname, c);
  if(computeSha2)   fprHashLine(buffer, sha2N,   humanReadableSz? fidx:sz, P(dSha2.getHash(),0),   fname, c);
  if(computeSha3)   fprHashLine(buffer, sha3N,   humanReadableSz? fidx:sz, P(dSha3.getHash(),0),   fname, c);
  if(computeKeccak) fprHashLine(buffer, KeccakN, humanReadableSz? fidx:sz, P(dKeccak.getHash(),0), fname, c);
  #undef P
  free(fname);

  outT[fidx] = buffer;
  if(thMax>1) sync( hashedCnt++; totalSzHashed += c*sz; )
  else{ hashedCnt++; totalSzHashed += c*sz; }

  return 0;
}

inline void fprHashLine(LPSTR& buffer, const string& algo, const size_t fSzIdx, 
     const std::pair<string,size_t>& P, LPCSTR fn, short& c)
 {
  LPCSTR hash = P.first.c_str(); size_t nHash = P.second;
  LPSTR p,s; chkAlloc(1, p);
  bool prWord = 0;
  
  if(algoPrefix){ 
    if(pretty){ chkRealloc(p, (size_t)hashNameW + 2); sprintf(p, "%-*.*s ", hashNameW,hashNameW,algo.c_str()); }
    else{ chkRealloc(p, algo.size() + 2);             sprintf(p, "%s ",                         algo.c_str()); }
    s = buffer; buffer = catStr({buffer, c>0? "\n":"", p}); free(s); prWord = true;
  }
  if(sizePrefix){ chkRealloc(p, (size_t)szWidth + 2);
    if(humanReadableSz){
      if(pretty) sprintf(p, "%-*.*s ", szWidth,szWidth,items[fileIndxes[fSzIdx]]->hsz); 
      else       sprintf(p, "%s ",                     items[fileIndxes[fSzIdx]]->hsz);
    }
    else{ if(pretty) sprintf(p, "%*zu ", szWidth,fSzIdx); else sprintf(p, "%zu ", fSzIdx); }
    s = buffer; buffer = catStr({buffer, (!prWord && c>0)? "\n":"", p}); free(s); prWord = true;
  }
  chkRealloc(p, (size_t)hashW + 1 + strlen(fn) + 1);
  
  if(nHash){ 
    if(lowerCase){ 
      if(pretty) sprintf(p, "%-*Ix %s", hashW,nHash, fn);
      else       sprintf(p, "%Ix %s",         nHash, fn);
    }
    else{
      if(pretty) sprintf(p, "%-*IX %s", hashW,nHash, fn);
      else       sprintf(p, "%IX %s",         nHash, fn);
    }
  }
  else {  s = nullptr;
    if(pretty) sprintf(p, "%-*.*s %s", hashW,hashW,lowerCase? hash:(s=toupper(P.first)), fn);
    else       sprintf(p, "%s %s",                 lowerCase? hash:(s=toupper(P.first)), fn);
    free(s);
  }
  s = buffer; buffer = catStr({buffer, (!prWord && c>0)? "\n":"", p}); free(s); c++;
  free(p); 
}

short process1File(LPSTR fn, LPCWSTR wfn, DWORD attr) {
  
  size_t fSz = 0; 
  LARGE_INTEGER fileSize;
  DWORD nBytesRead = 0;
  LPSTR p;
  
  auto f = CreateFileW(wfn, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, 0, NULL);
  if(f==INVALID_HANDLE_VALUE){ printErr(p=catStr({"  Error opening file: ",fn,"\n"}),sysErr,0); free(p); return 1; }
  
  if(!GetFileSizeEx(f, &fileSize)){ printErr(catStr({"  Error: could not determine file size: ",fn,"\n"}),sysErr,0); return 1; }
  fSz = fileSize.QuadPart;
  if((szLarger && fSz<leastSz) || (szSmaller && fSz>mostSz)) return 0;
  
  XXHash64 xxhash(0); CRC32 dCrc32; MD5 dMd5; SHA1 dSha1; SHA256 dSha2;       
  Keccak dKeccak(Keccak::Keccak256); SHA3 dSha3  (SHA3::Bits256);

  char* buffer; chkAlloc(BufferSize,buffer); short c = 0;
  while (ReadFile(f, buffer, (DWORD) BufferSize, &nBytesRead, nullptr) && nBytesRead){
    //fSz += nBytesRead;
    if (computeCrc32)  dCrc32 .add(buffer, nBytesRead);
    if (computeMd5)    dMd5   .add(buffer, nBytesRead);
    if (computeSha1)   dSha1  .add(buffer, nBytesRead);
    if (computeSha2)   dSha2  .add(buffer, nBytesRead);
    if (computeXX)     xxhash .add(buffer, nBytesRead); 
    if (computeKeccak) dKeccak.add(buffer, nBytesRead);
    if (computeSha3)   dSha3  .add(buffer, nBytesRead);

  }; auto Err = GetLastError(); CloseHandle(f);
  if(Err){ printErr(p=catStr({"  Error reading file: ",fn,"\n"}),10000+Err,0); free(p); return 1; }

  delete[] buffer;
  
  if( 1 == ((short)(computeCrc32?1:0) + (short)(computeMd5?1:0) + (short)(computeSha1?1:0) + (short)(computeSha2?1:0)
    + (short)(computeXX?1:0) + (short)(computeKeccak?1:0) + (short)(computeSha3?1:0))) pretty = false;
  
  short fszW = (short) std::to_string(fSz).length();

  // show results
  if(!noFname && baseNames){ char *slash = strrchr(fn,'/'), *bslash = strrchr(fn,'\\');
    if(slash!=nullptr) memmove(fn,slash+1,strlen(fn));
    else if(bslash!=nullptr) memmove(fn,bslash+1,strlen(fn));
  }
  LPSTR fname;
  if(tagSysHidden && ( (!noHidden && attr&FILE_ATTRIBUTE_HIDDEN) || (sysFiles && attr&FILE_ATTRIBUTE_SYSTEM) ) ) 
    fname = catStr({"*",fn});
  else fname = fn;

  #define P std::make_pair<string,size_t>
  if(computeCrc32)  { prHashLine(crcN,    fszW,fSz, P(dCrc32.getHash(),0),  fname); c++; }
  if(computeXX)     { prHashLine(xxN,     fszW,fSz, P("",xxhash.hash()),    fname); c++; }
  if(computeMd5)    { prHashLine(md5N,    fszW,fSz, P(dMd5.getHash(),0),    fname); c++; }
  if(computeSha1)   { prHashLine(sha1N,   fszW,fSz, P(dSha1.getHash(),0),   fname); c++; }
  if(computeSha2)   { prHashLine(sha2N,   fszW,fSz, P(dSha2.getHash(),0),   fname); c++; }
  if(computeSha3)   { prHashLine(sha3N,   fszW,fSz, P(dSha3.getHash(),0),   fname); c++; }
  if(computeKeccak) { prHashLine(KeccakN, fszW,fSz, P(dKeccak.getHash(),0), fname); c++; }
  #undef P

  hashedCnt++; totalSzHashed += c*fSz;
  return 0;
}

inline void prHashLine(const string& algo, const short fszW, const size_t fSz, const std::pair<string,size_t>& p, const LPCSTR fn){ 
 
  LPCSTR hash = p.first.c_str(); size_t nHash = p.second;
  
  if(pretty && algoPrefix){ if(sizePrefix){ 
                              if(humanReadableSz) flushOut("%-*.*s %s ",  hashNameW,hashNameW,algo.c_str(), humanSize(fSz));
                              else                flushOut("%-*.*s %zu ", hashNameW,hashNameW,algo.c_str(), fSz); }
                            else                  flushOut("%-*.*s ",     hashNameW,hashNameW,algo.c_str()); }
  else if(algoPrefix){ if(sizePrefix){ 
                         if(humanReadableSz) flushOut("%s %s ", algo.c_str(), humanSize(fSz));
                         else                flushOut("%s %zu ", algo.c_str(), fSz); }
                       else                  flushOut("%s ",     algo.c_str()); }
  else if(sizePrefix) if(humanReadableSz) flushOut("%s ", humanSize(fSz)); else flushOut("%zu ", fSz);
  
  if(nHash){ 
    if(lowerCase){ 
      if(pretty&&noFname) flushOut("%Ix\n",            nHash);
      else if(pretty)     flushOut("%-*Ix %s\n", hashW,nHash, noFname? "":fn);
      else                flushOut("%Ix %s\n",         nHash, noFname? "":fn); 
    }
    else{ 
      if(noFname)         flushOut("%IX\n",            nHash);
      else if(pretty)     flushOut("%-*IX %s\n", hashW,nHash, fn);
      else                flushOut("%IX %s\n",         nHash, fn); 
    }
    return;
  } 

  LPSTR s = nullptr;
  if(noFname)         flushOut("%s\n",                    lowerCase? hash:(s=toupper(p.first)));
  else if(pretty)     flushOut("%-*.*s %s\n", hashW,hashW,lowerCase? hash:(s=toupper(p.first)), fn);
  else                flushOut("%s %s\n",                 lowerCase? hash:(s=toupper(p.first)), fn);
  free(s);
}

template <typename T, class ... Ts>
inline void chkVectResz(size_t count, vector<T>& x, Ts&& ...args) {
  try { x.resize(count); }
  catch (const std::bad_alloc) {
    fprintf(stderr, "Error allocating memory (%zu x %zu bytes).\n\n", count, sizeof(T)); 
    exit(14);
  }
  chkVectResz(count, args...);
}

template <typename T, class ... Ts>
inline void chkAlloc(size_t count, T*& x, Ts&& ...args) {
  try { x = new T[count](); }
  catch (const std::bad_alloc) {
    fprintf(stderr, "Error allocating memory (%zu x %zu bytes).\n\n", count, sizeof(T)); 
    exit(15);
  }
  chkAlloc(count, args...);
}

template <typename T>
inline void chkRealloc(T*& x, size_t count) {
  x = (T*) realloc((void *)x, count * sizeof(T));
  if(nullptr == x){
    fprintf(stderr, "\n  Error: not enough memory (trying to reserve %zu x %zu bytes).\n\n", count, sizeof(T)); exit(14);
  }
}

inline void formatDur(__int64 dur, bool done) {
  size_t s = (size_t)(dur / 1000000); size_t ms = (size_t)(dur  - 1000000*s);
  UINT h = (UINT)(s / 3600); UINT m = (UINT)((s - 3600 * h) / 60);
  //flushErr("\nDone in %02lu:%02lu:%02lu.%lums\n\n", h, m, s, ms);

  size_t n = 65, cnt = 0; s = s % 60; CHAR lf[3] = "";
  CHAR* sh = nullptr, *sm = nullptr, *ss = nullptr; chkAlloc(n,sh,sm,ss);
  if(done){ flushErr("Done in "); lf[0] = '.'; lf[1] = '\n'; }
  else lf[0] = '\0';
  //if (d > 0) { snprintf(sd, 100, "%ld day", d);  cnt++; }; if (d > 1 || d == 0)  strcat(sd, "s");
  //h = 2; m = 14; s = 23;
  if(h>0){ snprintfA(sh, n, "%d hour", 2);   cnt++; }; if (h != 1)  strcat(sh, "s");
  if(m>0){ snprintfA(sm, n, "%d minute", m); cnt++; }; if (m != 1)  strcat(sm, "s");
  if(s>0){ snprintfA(ss, n, " second");    cnt++; }; if (ms>0 || s!=1) strcat(ss, "s");
  if(cnt==0){ flushErr("%.3f millisecond", (double)ms/1000); if (ms != 1000) flushErr("s%s",lf); else flushErr("%s",lf); return; }
  //if(d>0){ cnt--; flushErr("%s", sd); if (cnt > 0) flushErr(" and "); else flushErr(", "); }
  if(h>0){ cnt--; flushErr("%s", sh); if (cnt==0) flushErr(" and "); else flushErr(", "); }
  if(m>0){ cnt--; flushErr("%s", sm); if (cnt==0) flushErr(" and "); else flushErr(", "); }
  if(s>0){ flushErr("%lu.%06zu", s, ms); flushErr("%s", ss); }
  else{ flushErr("%.3f millisecond", (double)ms/1000); if (ms != 1000) flushErr("s"); }
  if(done) flushErr(".\n");
}

inline wchar_t* uf8toWide(LPCCH str) {
  auto dwCount = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, str, -1, nullptr, 0);
  if (0==dwCount){ DWORD errorMessageID = GetLastError();
    fprintf(stderr, "Error: MultiByteToWideChar() failed: %s\n",str); fflush(stderr);
    printErr(nullptr, 10000+errorMessageID, 59); }
  wchar_t *pText = nullptr; chkAlloc(dwCount, pText);
  if(0==MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, str, -1, pText, dwCount))
    printErr("Error: uf8toWide(): MultiByteToWideChar() failed\n", sysErr, 55);
  return pText;
} 

inline char* wide2uf8(LPCWSTR str) {
  auto dwCount = WideCharToMultiByte(CP_UTF8, 0, str, -1, nullptr, 0, nullptr, nullptr);
  if(0==dwCount){ DWORD errorID = GetLastError();
  fprintf(stderr, "Error: wide2uf8(): WideCharToMultiByte() failed.\n"); fflush(stderr); 
  printErr(nullptr, 10000+errorID, 57); }
  char *pText = nullptr; chkAlloc(dwCount, pText);
  if(0==WideCharToMultiByte(CP_UTF8, 0, str, -1, pText, dwCount, nullptr, nullptr))
    printErr("Error: uf8toWide(): WideCharToMultiByte() failed\n", sysErr, 58);
  return pText;
}

inline void flushErr(LPCSTR format, ...) {
  va_list args;
  va_start(args, format);
  vfprintf(stderr, format, args); fflush(stderr);
  va_end(args);
}
inline void flushOut(LPCSTR format, ...) {
  va_list args;
  va_start(args, format);
  vfprintf(stdout, format, args); fflush(stdout);
  va_end(args);
}

inline void printErr(LPCSTR msg, LONG errCode, int exitCode) {
  if (errCode > 10000) {  // query system
    errCode -= 10000;
    if(nullptr != msg) flushErr("\n  %s\n", msg);
    LPWSTR messageBuffer = nullptr;
    if(0 < FormatMessageW(FORMAT_MESSAGE_ALLOCATE_BUFFER | FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS,
      nullptr, (DWORD) errCode, 0, (LPWSTR)&messageBuffer, 0, nullptr)){
      LPSTR u8str = wide2uf8(messageBuffer); 
      size_t n = strlen(u8str) - 1; while(u8str[n]=='\n') u8str[(n--)] = 0;  // thank you
      flushErr("  (Err %d) %s\n\n", errCode, u8str); 
      LocalFree(messageBuffer); delete[] u8str; //free((void *)u8str);
    }
    if(exitCode!=0) exit(exitCode);
    return;
  }
  if(nullptr != msg) flushErr("\n  %s\n", msg);
  if(exitCode!=0) exit(exitCode);
}

inline void checkSnprintfA(HRESULT hRslt, size_t sz) {
  if(FAILED(hRslt)) {
    fprintf(stderr, "Error: snprintfA(): StringCchPrintfA() failed: ");
    if (hRslt==STRSAFE_E_INSUFFICIENT_BUFFER) fprintf(stderr, "INSUFFICIENT_BUFFER of %zu bytes\n", sz * sizeof(CHAR));
    else fprintf(stderr, "INVALID_PARAMETER: %zu chars not between 0 and %d\n", sz, STRSAFE_MAX_CCH);
    exit(18);
  }
  return;
}

inline void strCopy(LPSTR dst, size_t sz, LPCSTR src, bool truncate) {
  if(dst==nullptr) printErr("Error: strCopy(): destination cannot be null\n", 0, 15);
  auto hRslt = StringCchCopyA(dst, sz, src);
  if(hRslt==STRSAFE_E_INVALID_PARAMETER) {
    flushErr("\n  Error: StringCchCopyA() failed: destination size cannot be larger than %ld\n", STRSAFE_MAX_CCH);
    printErr(nullptr, 0, 16);
  } else if(!truncate && hRslt==STRSAFE_E_INSUFFICIENT_BUFFER)
    printErr("Error: StringCchCopyA() failed: insufficient buffer\n", 0, 17);
}

inline void wstrCopy(LPWSTR dst, size_t sz, LPWSTR src, bool truncate) {
  if(dst==nullptr) printErr("Error: wstrCopy(): destination cannot be null\n", 0, 15);
  auto hRslt = StringCchCopyW(dst, sz, src);
  if(hRslt==STRSAFE_E_INVALID_PARAMETER) {
    flushErr("\n  Error: StringCchCopyW() failed: destination size cannot be larger than %ld\n", STRSAFE_MAX_CCH);
    printErr(nullptr, 0, 16);
  } else if(!truncate && hRslt==STRSAFE_E_INSUFFICIENT_BUFFER)
    printErr("Error: StringCchCopyW() failed: insufficient buffer\n", 0, 17);
}

inline LPSTR catStr(std::initializer_list<LPCSTR> list){
  size_t sz = 0; 
  HRESULT hRslt = S_OK;
  LPSTR buff; chkAlloc(1,buff); buff[0] = '\0';
  for (auto x : list){
    chkRealloc(buff, sz = 1 + strlen(x) + strlen(buff));
    hRslt = StringCchCatA(buff, sz, x);
    if(FAILED(hRslt)) {
      fprintf(stderr, "Error: catStr(): StringCchCatA() failed: ");
      if(hRslt==STRSAFE_E_INSUFFICIENT_BUFFER) fprintf(stderr, "INSUFFICIENT_BUFFER of %zu bytes\n", sz * sizeof(CHAR));
      else printErr(nullptr, sysErr, 23);
      exit(16);
    }
  }
  return buff;
}

inline LPWSTR catWstr(std::initializer_list<LPCWSTR> list){
  size_t sz = 0; 
  HRESULT hRslt = S_OK;
  LPWSTR buff; chkAlloc(1,buff); buff[0] = '\0';
  for (auto x : list){
    sz = 1 + lstrlenW(x) + lstrlenW(buff);
    chkRealloc(buff, sz);
    hRslt = StringCchCatW(buff, sz, x);
    if(FAILED(hRslt)) {
      fprintf(stderr, "Error: catWstr(): StringCchCatW() failed: ");
      if(hRslt==STRSAFE_E_INSUFFICIENT_BUFFER) fprintf(stderr, "INSUFFICIENT_BUFFER of %zu bytes\n", sz * sizeof(WCHAR));
      else printErr(nullptr, sysErr, 24);
      exit(16);
    }
  }
  return buff;
}
