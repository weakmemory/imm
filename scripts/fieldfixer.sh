#!/bin/bash
sed -i "s|\([a-zA-Z0-9]*\)\.(\([a-zA-Z0-9\_]*\))|(\2 \1)|g" src/*/*.v
