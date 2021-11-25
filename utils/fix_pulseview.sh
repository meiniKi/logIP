#!/usr/bin/env fish
pushd /tmp
wget -O fx2lafw-sigrok-fx2-8ch.zip https://github.com/wuxx/nanoDLA/files/4567609/fx2lafw-sigrok-fx2-8ch.zip
unzip fx2lafw-sigrok-fx2-8ch.zip
mkdir -p ~/.local/share/sigrok-firmware/
cp -v fx2lafw-sigrok-fx2-8ch.fw ~/.local/share/sigrok-firmware/fx2lafw-sigrok-fx2-8ch.fw
popd