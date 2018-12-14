# How to login to INRIA CI runners

1.) Generate key pair "inria-ci" and install key pair at https://ci.inria.fr
See https://wiki.inria.fr/ciportal/Slaves_Access_Tutorial

2.) Add this to .ssh/config
(The last line is for tunneling through a proxy and not needed when you don't have a proxy)
```
Host ci-ssh.inria.fr
    Hostname      ci-ssh.inria.fr
    IdentityFile  ~/.ssh/inria-ci
    ProxyCommand  nc -X 5 -x <proxy>:<port> %h %p
```

3.) Login once manually using
```
ssh <username>@ci-ssh.inria.fr
exit
```

4.) run script
```
./login_runners.sh <your_inria_ci_user_id>
```
# Hints on Runner maintenance work

- All runners have a small cygwin installation for maintenance under `C:\bin\cygwin_ci_maintenance`

- For deleting cygwin created folders it is usually better to run cygwin as admin and rm -rf from there (arbitrary folders under C:\ are accessible as /cygdrive/c/). Cygwin created folders can have weird access rights (from cygwin posix emulation) and be hard to delete from explorer

# Setup of CI maintenance cygwin

Use the script `CiRunnerMaintenance_InstallCygwin.bat`.

- For a default installation no parameters are required.
- The cygwin setup is downloaded by the script automatically and need not be provided.
- `CiRunnerMaintenance_ConfigureCygwinProfile.sh` must be in the same folder.

## Parameters of CiRunnerMaintenance_InstallCygwin.bat

#### -arch

Set the target architecture.

Possible values:

- 32: Install/build Cygwin, ocaml and coq for 32 bit windows

- 64: Install/build Cygwin, ocaml and coq for 64 bit windows

Default value: 64

#### -destcyg

Destination folder in which Cygwin is installed.

This must be an absolute path in Windows format (with drive letter and \\).

Default value: `C:\bin\cygwin_ci_maintenance`

#### -proxy

Internet proxy setting for downloading Cygwin, ocaml and coq.

The format is <server>:<port>, e.g. proxy.mycompany.com:911

The same proxy is used for HTTP, HTTPS and FTP.
If you need separate proxies for separate protocols, please put your proxies directly into configure_profile.sh.

Default value: Value of HTTP_PROXY environment variable or none if this variable does not exist.

**ATTENTION:** With the --proxy setting of the Cygwin setup, it is possible to
supply a proxy server, but if this parameter is "", Cygwin setup might use proxy
settings from previous setups. If you once did a Cygwin setup behind a firewall
and now want to do a Cygwin setup without a firewall, use the -cygquiet=N
setting to perform a GUI install, where you can adjust the proxy setting.

#### -cygrepo

The online repository, from which Cygwin packages are downloaded.

Default value: `http://mirror.easyname.at/cygwin`

#### -cygcache

The local cache folder for Cygwin repositories.

#### -cyglocal

Control if the Cygwin setup uses the latest version from the internet or the version as is in the local folder.

Possible values:

- Y: Install exactly the Cygwin version from the local repository cache.
   Don't update from the internet.

- N: Download the latest Cygwin version from the internet.
   Update the local repository cache with the latest version.

Default value: N

#### -cygquiet

Control if the Cygwin setup runs quitely or interactive.

Possible values:

- Y: Install Cygwin quitely without user interaction.

- N: Install Cygwin interactively (allows to select additional packages).

Default value: Y

