#!/bin/sh
sed -e "s/^\*\*/---\n#/g" "$1" | sed -e "s/^\+/*/g" | sed -e "s/#+BEGIN_SRC /\`\`\`/g"  | sed -e "s/#+END_SRC/\`\`\`/g" | sed -e "s/^\*\*/---\n#/g"


