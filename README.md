# xcc

xcc is an attempt to write a basic C compiler, based on *Rui Ueyama's* awesome [8cc](https://github.com/rui314/8cc).

Supports x86_64 Linux only, you can use [WSL](https://docs.microsoft.com/en-us/windows/wsl/install-win10?redirectedfrom=MSDN) to run on windows platform.

Build
===
Simply run make to build.

```
make
```

To run tests:
```
make test
```
Testing as of now is a simple bash script, to add more tests, edit [test.sh](https://github.com/utkarsh261/xcc/blob/master/test.sh#L20).

**Current Progress:**

* Supports basic arithmetic operations  (+. -, *, /).
