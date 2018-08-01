// (C) 2016 Intel Deutschland GmbH
// Author: Michael Soegtrop
// Released to the public under CC0
// See https://creativecommons.org/publicdomain/zero/1.0/

// Windows drop in repacement for Linux ln
// Supports command form "ln TARGET LINK_NAME"
// Supports -s and -f options
// Does not support hard links to folders (but symlinks are ok)

#include <windows.h>
#include <stdio.h>
#include <tchar.h>

// Cygwin MinGW doesn't have this Vista++ function in windows.h
#ifdef UNICODE
    WINBASEAPI BOOLEAN APIENTRY CreateSymbolicLinkW ( LPCWSTR, LPCWSTR, DWORD );
    #define CreateSymbolicLink  CreateSymbolicLinkW
    #define CommandLineToArgv CommandLineToArgvW
#else
    WINBASEAPI BOOLEAN APIENTRY CreateSymbolicLinkA ( LPCSTR, LPCSTR, DWORD );
    #define CreateSymbolicLink  CreateSymbolicLinkA
    #define CommandLineToArgv CommandLineToArgvA
#endif
#define SYMBOLIC_LINK_FLAG_DIRECTORY 1

int WINAPI WinMain( HINSTANCE hInstance, HINSTANCE hPrevInstance, LPSTR lpCmdLineA, int nShowCmd )
{
    int iarg;
    BOOL symbolic = FALSE;
    BOOL force = FALSE;
    BOOL folder;
    const _TCHAR *target;
    const _TCHAR *link;
    LPTSTR lpCmdLine; 
    int argc;
    LPTSTR *argv;

    // Parse command line
    // This is done explicitly here for two reasons
    // 1.) MinGW doesn't seem to support _tmain, wWinMain and the like
    // 2.) We want to make sure that CommandLineToArgv is used
    lpCmdLine = GetCommandLine();
    argv = CommandLineToArgv( lpCmdLine, &argc );
    
    // Get target and link name
    if( argc<3 )
    {
        _ftprintf( stderr, _T("Expecting at least 2 arguments, got %d\n"), argc-1 );
        return 1;
    }
    target = argv[argc-2];
    link = argv[argc-1];

    // Parse options
    // The last two arguments are interpreted as file names
    // All other arguments must be -s or -f os multi letter options like -sf
    for(iarg=1; iarg<argc-2; iarg++ )
    {
        const _TCHAR *pos = argv[iarg]; 
        if( *pos != _T('-') )
        {
            _ftprintf( stderr, _T("Command line option expected in argument %d\n"), iarg );
            return 1;
        }
        pos ++;

        while( *pos )
        {
            switch( *pos )
            {
                case _T('s') : symbolic = TRUE; break;
                case _T('f') : force = TRUE; break;
                default : 
                    _ftprintf( stderr, _T("Unknown option '%c'\n"), *pos );
                    return 1;
            }
            pos ++;
        }
    }
    
    #ifdef IGNORE_SYMBOLIC
        symbolic = FALSE;
    #endif
    
    // Check if link already exists - delete it if force is given or abort
    {
        if( GetFileAttributes(link) != INVALID_FILE_ATTRIBUTES )
        {
            if( force )
            {
                if( !DeleteFile( link ) )
                {
                    _ftprintf( stderr, _T("Error deleting file '%s'\n"), link );
                    return 1;
                }
            }
            else
            {
                _ftprintf( stderr, _T("File '%s' exists!\n"), link );
                return 1;
            }
        }
    }
    
    // Check if target is a folder
    folder = ( (GetFileAttributes(target) & FILE_ATTRIBUTE_DIRECTORY) ) != 0;
    
    // Create link
    if(symbolic)
    {
        if( !CreateSymbolicLink( link, target, folder ? SYMBOLIC_LINK_FLAG_DIRECTORY : 0 ) )
        {
            _ftprintf( stderr, _T("Error creating symbolic link '%s' -> '%s'!\n"), link, target );
            return 1;
        }
    }
    else
    {
        if( folder )
        {
            _ftprintf( stderr, _T("Cannot create hard link to folder") );
            return 1;
        }
        else
        {
            if( !CreateHardLink( link, target, NULL ) )
            {
                _ftprintf( stderr, _T("Error creating hard link '%s' -> '%s'!\n"), link, target );
                return 1;
            }
        }
    }
    
    // Everything is fine
    return 0;
}
