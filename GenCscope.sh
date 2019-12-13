#!/bin/bash
arch="i386"
if [ "$1" ];then
	arch=$1
fi

if [ -f "./cscope.files" ];then
	rm ./cscope*
fi
touch cscope.files
find . -path "./arch" -prune -o -path "./include/asm" -prune -o -name "*.[chS]" >> cscope.files
sed -i "/\.\/arch/d;/\.\/include\/asm/d" cscope.files >> cscope.files
find ./arch/$arch -name "*.[chS]" >> cscope.files
find ./include/asm-generic -name "*.[chS]" >> cscope.files
find ./include/asm-$arch -name "*.[chS]" >> cscope.files
cscope -Rbqk
ctags -R
echo "finished!"
