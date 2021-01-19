#!/bin/bash
# Invoke as ./script.sh MYLIBRARYFOLDER

pattern() {
  PATTERN="s/^\(\s*\)$1/\1#[global]\n\1$1/g"
  sed -i "$PATTERN" $2
}

for i in $(find $1 -name "*.v");
do
pattern "Hint Resolve" $i
pattern "Hint Immediate" $i
pattern "Hint Extern" $i
pattern "Hint Constructors" $i
pattern "Hint Unfold" $i
pattern "Hint Variables" $i
pattern "Hint Constants" $i
pattern "Hint Transparent" $i
pattern "Hint Opaque" $i
done
