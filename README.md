# TyDe 2024 Title

The full working code for the
[TyDe 2024](icfp24.sigplan.org/home/tyde-2024)
paper submitted by
[Thomas Ekström Hansen ![ORCID logo](https://info.orcid.org/wp-content/uploads/2019/11/orcid_16x16.png)](https://orcid.org/0000-0002-2472-9694)
and
[Edwin Brady ![ORCID logo](https://info.orcid.org/wp-content/uploads/2019/11/orcid_16x16.png)](https://orcid.org/0000-0002-9734-367X).


## Building

### Pre-requisites

A working install of the Idris2 compiler >= v0.7.0 is required. The easiest way
to get this set up is to install Idris2 via
[pack](https://github.com/stefan-hoeck/idris2-pack).

### Compiling

With a working `idris2` in your `$PATH`, the files can be compiled by running

```
idris2 --build tyde24.ipkg
```

### REPL

An interactive REPL session can be started by running

```
idris2 --repl tyde24.ipkg
```

This will load the `Generic` module by default. The other modules can be loaded
by running the REPL command

```
:module ModuleName
```

(replacing `ModuleName` with the name of the module to additionally load.)

After a module has been loaded, its contents can be browsed via the REPL command

```
:browse ModuleName
```


## LICENSE

The code in this repository is licensed under the terms of the `BSD-3-Clause`
license (see the [LICENSE](LICENSE) file).

