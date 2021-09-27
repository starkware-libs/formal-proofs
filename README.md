# Cairo verification using Lean

## To build from Github

Install Lean and VS Code following these [instructions](https://leanprover-community.github.io/get_started.html).
Navigate to the directory where you want to install download the repository,
and type the following commands (on Linux or OS/X):
```
  leanproject get git@github.com:starkware-libs/formal-proofs.git
  cd formal-proofs
  leanproject build
```
This will fetch the repository, fetch the mathlib library, and compile and check the files.
You can then open the top folder in VS Code and browse the `.lean` files.

## To build from this folder

If you have obtained the folder some other way, install Lean as above. Then, from inside the folder, issue the following commands:
```
  leanproject get-mathlib
  leanproject build
```
This will fetch the mathlib library and then compile and check the files. You can then open the folder in VS Code and browse the `.lean` files.

## To build using Gitpod

If you have a Gitpod account or are willing to sign up for one, just point your browser to [https://gitpod.io/#/https://github.com/starkware-libs/formal-proofs](https://gitpod.io/#/https://github.com/starkware-libs/formal-proofs).
This will create a virtual machine in the cloud, install Lean and mathlib, and compile
and check all the files in the repository.
You can then browse them with VS Code in your browser window.


