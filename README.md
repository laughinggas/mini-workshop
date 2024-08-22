This is a mini workshop designed to introduce the beginner-level user to Lean 4. In order to access this repository, please use the following instructions:
1. Install Lean using the instructions here: [Get started with Lean](https://leanprover-community.github.io/get_started.html) . This will install VSCode, git, elan and Lean, all of which are required.
2. Get a local copy of this repository:
   a. Open a terminal.
   b. If you have not logged in since you installed Lean and mathlib, then you may need to first type source ~/.profile or source ~/.bash_profile depending on your OS. If you are on Windows, and don't know how to do this, another option is to restart your computer.
   c. Go to the directory where you would like this package to live. You do not need to create a new folder yourself, the next command will create a mathematics_in_lean (replace with what you would like to name the folder) subfolder for you.
   d. Run `git clone https://github.com/laughinggas/mini-workshop` .
   e. Run `cd mathematics_in_lean`
   f. Run `lake exe cache get`
   g. Launch VSCode
   h. If you launched VS Code from a menu, on the main screen, or in the File menu, click "Open folder" (just "Open" on a Mac), and choose the folder mathematics_in_lean (not one of its subfolders).
   i. Using the file explorer on the left-hand side, explore everything you want. Open the file Basic.lean. Make sure it compiles (all the vertical orange lines disappear).

Happy Leaning!
