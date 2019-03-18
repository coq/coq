// MinGW personality wrapper for pkgconf
// This is an excutable replacement for the shell scripts /bin/ARCH-pkg-config
// Compile with e.g.
// gcc pkg-config.c -DARCH=x86_64-w64-mingw32 -o pkg-config.exe
// gcc pkg-config.c -DARCH=i686-w64-mingw32 -o pkg-config.exe
// ATTENTION: Do not compile with MinGW-gcc, compile with cygwin gcc!
//
// To test it execute e.g.
// $ ./pkg-config --path zlib
// /usr/x86_64-w64-mingw32/sys-root/mingw/lib/pkgconfig/zlib.pc

#include <unistd.h>

#define STRINGIFY1(arg) #arg
#define STRINGIFY(arg) STRINGIFY1(arg)

int main(int argc, char *argv[])
{
    // +1 for extra argument, +1 for trailing NULL
    char * argvnew[argc+2];
    int id=0, is=0;

    argvnew[id++] = argv[is++];
    argvnew[id++] = "--personality="STRINGIFY(ARCH);
    while( is<argc ) argvnew[id++] = argv[is++];
    argvnew[id++] = 0;

    return execv("/usr/bin/pkgconf", argvnew);
}
