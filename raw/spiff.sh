#!/bin/bash

echo "Prompt,Strongly Agree,Agree,Uncertain,Disagree,Strongly Disagree" > label.txt

cat $1                      | #
 hxnormalize -x -e -l 256   | # \
 hxclean                    | # | Pull out only response data
 hxselect '.style_58 table' | # /
 sed 's/<\/table>/\n/g'     | # Split data to 1 question per line
 sed 's/<table id="test-responses-nonmatrix-/"/g' | # \
 sed 's/ style="[^"]*"//g'                        | # | Remove crud
 sed 's/<td>series<\/td>//g'                      | # |
 sed 's/<td>value<\/td>//g'                       | # |
 sed 's/><tbody><tr><\/tr>//g'                    | # |
 sed 's/<\/tbody>//g'                             | # /
 sed 's/<td>0<\/td>/SA /g' | # \
 sed 's/<td>1<\/td>/A /g'  | # | Response labels (removed later)
 sed 's/<td>2<\/td>/U /g'  | # |
 sed 's/<td>3<\/td>/D /g'  | # |
 sed 's/<td>4<\/td>/SD /g' | # /
 sed 's/\.0//g'       | # \
 sed 's/<td>//g'      | # | Remove more crud
 sed 's/<\/td>//g'    | # |
 sed 's/<tr>/ /g'     | # |
 sed 's/<\/tr>//g'    | # /
 sed '/classification/d' | # \
 sed '/GPA/d'            | # | Remove demographic questions
 sed '/main reason/d'    | # |
 sed '/expected grade/d' | # /
 # Fill in zeros for missing data (ugh why)
 sed 's/" A \([0-9]*\) U \([0-9]*\) D \([0-9]*\) SD \([0-9]*\)$/" SA 0 A \1 U \2 D \3 SD \4/g'  |
 sed 's/" SA \([0-9]*\) U \([0-9]*\) D \([0-9]*\) SD \([0-9]*\)$/" SA \1 A 0 U \2 D \3 SD \4/g' |
 sed 's/" SA \([0-9]*\) A \([0-9]*\) D \([0-9]*\) SD \([0-9]*\)$/" SA \1 A \2 U 0 D \3 SD \4/g' |
 sed 's/" SA \([0-9]*\) A \([0-9]*\) U \([0-9]*\) SD \([0-9]*\)$/" SA \1 A \2 U \3 D 0 SD \4/g' |
 sed 's/" SA \([0-9]*\) A \([0-9]*\) U \([0-9]*\) D \([0-9]*\)$/" SA \1 A \2 U \3 D \4 SD 0/g'  |
 sed 's/" U \([0-9]*\) D \([0-9]*\) SD \([0-9]*\)$/" SA 0 A 0 U \1 D \2 SD \3/g'  |
 sed 's/" A \([0-9]*\) D \([0-9]*\) SD \([0-9]*\)$/" SA 0 A \1 U 0 D \2 SD \3/g'  |
 sed 's/" A \([0-9]*\) U \([0-9]*\) SD \([0-9]*\)$/" SA 0 A \1 U \2 D 0 SD \3/g'  |
 sed 's/" A \([0-9]*\) U \([0-9]*\) D \([0-9]*\)$/" SA 0 A \1 U \2 D \3 SD 0/g'   |
 sed 's/" SA \([0-9]*\) D \([0-9]*\) SD \([0-9]*\)$/" SA \1 A 0 U 0 D \2 SD \3/g' |
 sed 's/" SA \([0-9]*\) U \([0-9]*\) SD \([0-9]*\)$/" SA \1 A 0 U \2 D 0 SD \3/g' |
 sed 's/" SA \([0-9]*\) U \([0-9]*\) D \([0-9]*\)$/" SA \1 A 0 U \2 D \3 SD 0/g'  |
 sed 's/" SA \([0-9]*\) A \([0-9]*\) SD \([0-9]*\)$/" SA \1 A \2 U 0 D 0 SD \3/g' |
 sed 's/" SA \([0-9]*\) A \([0-9]*\) D \([0-9]*\)$/" SA \1 A \2 U 0 D \3 SD 0/g'  |
 sed 's/" SA \([0-9]*\) A \([0-9]*\) U \([0-9]*\)$/" SA \1 A \2 U \3 D 0 SD 0/g'  |
 sed 's/" D \([0-9]*\) SD \([0-9]*\)$/" SA 0 A 0 U 0 D \1 SD \2/g'   |
 sed 's/" U \([0-9]*\) SD \([0-9]*\)$/" SA 0 A 0 U \1 D 0 SD \2/g'   |
 sed 's/" A \([0-9]*\) SD \([0-9]*\)$/" SA 0 A \1 U 0 D 0 SD \2/g'   |
 sed 's/" SA \([0-9]*\) SD \([0-9]*\)$/" SA \1 A 0 U 0 D 0 SD \2/g'  |
 sed 's/" U \([0-9]*\) D \([0-9]*\)$/" SA 0 A 0 U \1 D \2 SD 0/g'    |
 sed 's/" A \([0-9]*\) D \([0-9]*\)$/" SA 0 A \1 U 0 D \2 SD 0/g'    |
 sed 's/" SA \([0-9]*\) D \([0-9]*\)$/" SA \1 A 0 U 0 D \2 SD 0/g'   |
 sed 's/" A \([0-9]*\) U \([0-9]*\)$/" SA 0 A \1 U \2 D 0 SD 0/g'    |
 sed 's/" SA \([0-9]*\) U \([0-9]*\)$/" SA \1 A 0 U \2 D 0 SD 0/g'   |
 sed 's/" SA \([0-9]*\) A \([0-9]*\)$/" SA \1 A \2 U 0 D 0 SD 0/g'   |
 sed 's/" SA \([0-9]*\)$/" SA \1 A 0 U 0 D 0 SD 0/g' |
 sed 's/" A \([0-9]*\)$/" SA 0 A \1 U 0 D 0 SD 0/g'  |
 sed 's/" U \([0-9]*\)$/" SA 0 A 0 U \1 D 0 SD 0/g'  |
 sed 's/" D \([0-9]*\)$/" SA 0 A 0 U 0 D \1 SD 0/g'  |
 sed 's/" SD \([0-9]*\)$/" SA 0 A 0 U 0 D 0 SD \1/g' |
 sed 's/ SA /,/g' | # \
 sed 's/ A /,/g'  | # | Remove labels
 sed 's/ U /,/g'  | # |
 sed 's/ D /,/g'  | # |
 sed 's/ SD /,/g' | # /
 cat > data.csv

cat label.txt data.csv > evals.csv

rm label.txt data.csv
