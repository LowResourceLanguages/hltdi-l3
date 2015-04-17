# {(C)V(C) [CV(C)]} CV

-> start

start -> C       [C]
C -> CV          [V]
CV -> CVC        [C]
CVC -> end       [V]

##start -> CV      [V]
##CV -> CVC        [C]
##CVC -> CVCC      [C]
##CVC -> CVCV      [V]
##CVCC -> CVCV     [V]
##CVCV -> CVCVC    [C]
##CVCVC -> CVCVCC  [C]
##CVCVC -> end     [V]
##CVCVCC -> end    [V]

end ->
##CV ->                
##CVCV ->
