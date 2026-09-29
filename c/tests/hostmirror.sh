#!/bin/bash
# A fast host mirror of the bare-metal build, for debugging runs that take
# the Sail emulator an hour: the same runtime sources, configuration
# headers, main.c and in-memory file system (htif.c with -DHOST_MIRROR),
# compiled natively; the runtime's open/read/write/lseek/close/stat/
# unlink/rename/opendir/readdir/closedir calls are redirected to htif.c's
# versions by macros (tests/hostmirror.h). Same argv/FILES/RUNPARAM
# conventions as the Makefile.
#   tests/hostmirror.sh OUT PROG 'ARGS' 'FILES' [RUNPARAM]
set -e
cd "$(dirname "$0")/.."
OUT=$1; PROG=$2; ARGS=$3; FILES=$4; RP=${5:-}
RT=../vendor/ocaml-4.14.2/runtime
D=build/mirror-$(basename $OUT); mkdir -p $D
src/gen_prims.sh $RT $(realpath $D)/prims.c
# embedded files as a C table instead of .incbin
python3 - "$D/embed.c" /prog=$PROG $FILES <<'PY'
import sys
out=open(sys.argv[1],'w'); ent=[]
for i,spec in enumerate(sys.argv[2:]):
    path,f=spec.split('=',1); b=open(f,'rb').read()
    out.write(f"static const char f{i}[] = {{{','.join(str(x) for x in b)},0}};\n")
    ent.append(f'{{"{path}", f{i}, f{i}+{len(b)}}}')
out.write("struct embedded_file { const char *path; const char *start; const char *end; };\n")
out.write("const struct embedded_file embedded_files[] = {"+",".join(ent)+",{0,0,0}};\n")
PY
RTS=$(python3 -c "
s=open('Makefile').read(); a=s.index('RT_SRC :='); b=s.index('RT_C :=')
print(' '.join('$RT/'+x+'.c' for x in s[a+9:b].replace('\\\\',' ').split()))")
CF="-O1 -w -fno-strict-aliasing -fwrapv -fno-common -U_FORTIFY_SOURCE -DCAML_NAME_SPACE -DCAMLDLLIMPORT= -DSHRINKED_GNUC -Isrc/config/caml -Isrc/config -I$RT"
H=$(realpath tests/hostmirror.h)
sed 's/^void _exit/void mf_exit_unused/; s/^int _getpid/int mf_getpid_unused/; s/^int _isatty/int mf_isatty/; s/^int rename(/int mf_rename(/; s/^void \*_sbrk(/static void *mf_sbrk_unused(/' src/htif.c > $D/htif.c
gcc $CF -include $H -DMIRROR_WRITE -c -o $D/unix.o $RT/unix.c
gcc $CF -c -o $D/extern.o $RT/extern.c   # no FS calls; has its own static write()
gcc $CF -include $H "-DOCAML_ARGS=$ARGS" "-DOCAMLRUNPARAM=\"$RP\"" -o $OUT \
  src/main.c src/stubs.c $D/prims.c $D/embed.c $D/unix.o $D/extern.o $(echo $RTS | sed "s|$RT/unix.c||; s|$RT/extern.c||") \
  -DHOST_MIRROR -Isrc $D/htif.c -lm
