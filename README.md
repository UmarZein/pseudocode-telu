
if you are running on windows. Please go to `C:/msys64/mingw64/lib/` and do `mv libpthread.dll.a libpthread.dll.a.bak`. Because that has caused issues on windows machines regarding the linking process, specifically with multiple definitions of `pthread_*`
