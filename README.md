This is a mini workshop designed to introduce the beginner-level user to Lean 4. First, please install Lean using the instructions here: [Get started with Lean](https://leanprover-community.github.io/get_started.html) . This will install VSCode, git, elan and Lean, all of which are required.

In order to get a local copy of this repository, use the following instructions(as taken from the official website of Lean):
1. Open a terminal.
2. If you have not logged in since you installed Lean and mathlib, then you may need to first type source ~/.profile or source ~/.bash_profile depending on your OS. If you are on Windows, and don't know how to do this, another option is to restart your computer.
3. Go to the directory where you would like this package to live. You do not need to create a new folder yourself, the next command will create a `mathematics_in_lean` (replace with what you would like to name the folder) subfolder for you.
4. Run `git clone https://github.com/laughinggas/mini-workshop` .
5. Run `cd mathematics_in_lean` .
6. Run `lake exe cache get` .
7. Launch VSCode, either through your application menu or by typing code .. (MacOS users need to take a one-off [extra step](https://code.visualstudio.com/docs/setup/mac#_launching-from-the-command-line) to be able to launch VS Code from the command line.)
8. If you launched VS Code from a menu, on the main screen, or in the File menu, click "Open folder" (just "Open" on a Mac), and choose the folder mathematics_in_lean (not one of its subfolders).
9. Using the file explorer on the left-hand side, explore everything you want. Open the file Basic.lean inside the folder `MiniWorkshop`. Make sure it compiles (all the vertical orange lines disappear).

Happy Leaning!
