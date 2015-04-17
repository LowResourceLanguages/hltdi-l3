%this is the romanization Prolog code
%it has dictionary of the Geez Fidel and the roman equivalent character set
%the code accepts a Geez string and give back the roman translitration

%Oct 14,2011
trans([],[]).
trans([Am|AmhT],Rom):-
	trans(AmhT,RomX),
	letter([Am],X),
	append(X,RomX,Rom).

romanize(A,B):-
	atom_chars(A,AA),
	trans(AA,BB),
	atom_chars(B,BB).

letter([' '],[' ']).

%ሀ
letter([ሀ],[h,e]).
letter([ሁ],[h,u]).
letter([ሂ],[h,i]).
letter([ሃ],[h,a]).
letter([ሄ],[h,'E']).
letter([ህ],[h,'I']).
letter([ሆ],[h,o]).

%ለ
letter([ለ],[l,e]).
letter([ሉ],[l,u]).
letter([ሊ],[l,i]).
letter([ላ],[l,a]).
letter([ሌ],[l,'E']).
letter([ል],[l,'I']).
letter([ሎ],[l,o]).

%ሐ
letter([ሐ],['H',e]).
letter([ሑ],['H',u]).
letter([ሒ],['H',i]).
letter([ሓ],['H',a]).
letter([ሔ],['H','E']).
letter([ሕ],['H','I']).
letter([ሖ],['H',o]).

%መ
letter([መ],[m,e]).
letter([ሙ],[m,u]).
letter([ሚ],[m,i]).
letter([ማ],[m,a]).
letter([ሜ],[m,'E']).
letter([ም],[m,'I']).
letter([ሞ],[m,o]).

%ሠ  ??
letter([ሠ],['S',e]).
letter([ሡ],['S',u]).
letter([ሢ],['S',i]).
letter([ሣ],['S',a]).
letter([ሤ],['S','E']).
letter([ሥ],['S','I']).
letter([ሦ],['S',o]).

%ረ 
letter([ረ],[r,e]).
letter([ሩ],[r,u]).
letter([ሪ],[r,i]).
letter([ራ],[r,a]).
letter([ሬ],[r,'E']).
letter([ር],[r,'I']).
letter([ሮ],[r,o]).

%ሰ 
letter([ሰ],[s,e]).
letter([ሱ],[s,u]).
letter([ሲ],[s,i]).
letter([ሳ],[s,a]).
letter([ሴ],[s,'E']).
letter([ስ],[s,'I']).
letter([ሶ],[s,o]).

%ሸ
letter([ሸ],[x,e]).
letter([ሹ],[x,u]).
letter([ሺ],[x,i]).
letter([ሻ],[x,a]).
letter([ሼ],[x,'E']).
letter([ሽ],[x,'I']).
letter([ሾ],[x,o]). 

%ቀ
letter([ቀ],[q,e]).
letter([ቁ],[q,u]).
letter([ቂ],[q,i]).
letter([ቃ],[q,a]).
letter([ቄ],[q,'E']).
letter([ቅ],[q,'I']).
letter([ቆ],[q,o]). 

%በ 
letter([በ],[b,e]).
letter([ቡ],[b,u]).
letter([ቢ],[b,i]).
letter([ባ],[b,a]).
letter([ቤ],[b,'E']).
letter([ብ],[b,'I']).
letter([ቦ],[b,o]). 

%ተ 
letter([ተ],[t,e]).
letter([ቱ],[t,u]).
letter([ቲ],[t,i]).
letter([ታ],[t,a]).
letter([ቴ],[t,'E']).
letter([ት],[t,'I']).
letter([ቶ],[t,o]). 

%ቸ 
letter([ቸ],[c,e]).
letter([ቹ],[c,u]).
letter([ቺ],[c,i]).
letter([ቻ],[c,a]).
letter([ቼ],[c,'E']).
letter([ች],[c,'I']).
letter([ቾ],[c,o]). 


%ነ 
letter([ነ],[n,e]).
letter([ኑ],[n,u]).
letter([ኒ],[n,i]).
letter([ና],[n,a]).
letter([ኔ],[n,'E']).
letter([ን],[n,'I']).
letter([ኖ],[n,o]). 

%ኘ 
letter([ፐ],[p,e]).
letter([ፑ],[p,u]).
letter([ፒ],[p,i]).
letter([ፓ],[p,a]).
letter([ፔ],[p,'E']).
letter([ፕ],[p,'I']).
letter([ፖ],[p,o]). 

%አ 
letter([አ],['A',e]).
letter([ኡ],['A',u]).
letter([ኢ],['A',i]).
letter([ኣ],['A',a]).
letter([ኤ],['A','E']).
letter([እ],['A','I']).
letter([ኦ],['A',o]). 

%ከ 
letter([ከ],[k,e]).
letter([ኩ],[k,u]).
letter([ኪ],[k,i]).
letter([ካ],[k,a]).
letter([ኬ],[k,'E']).
letter([ክ],[k,'I']).
letter([ኮ],[k,o]). 

%ኸ 
letter([ኸ],['K',e]).
letter([ኹ],['K',u]).
letter([ኺ],['K',i]).
letter([ኻ],['K',a]).
letter([ኼ],['K','E']).
letter([ኽ],['K','I']).
letter([ኾ],['K',o]). 

%ወ 
letter([ወ],[w,e]).
letter([ዉ],[w,u]).
letter([ዊ],[w,i]).
letter([ዋ],[w,a]).
letter([ዌ],[w,'E']).
letter([ው],[w,'I']).
letter([ዎ],[w,o]). 

%ዐ
letter([ዐ],['A',e]).
letter([ዑ],['A',u]).
letter([ዒ],['A',i]).
letter([ዓ],['A',a]).
letter([ዔ],['A','E']).
letter([ዕ],['A','I']).
letter([ዖ],['A',o]). 

%ዘ 
letter([ዘ],[z,e]).
letter([ዙ],[z,u]).
letter([ዚ],[z,i]).
letter([ዛ],[z,a]).
letter([ዜ],[z,'E']).
letter([ዝ],[z,'I']).
letter([ዞ],[z,o]). 

%ዠ 
letter([ዠ],['Z',e]).
letter([ዡ],['Z',u]).
letter([ዢ],['Z',i]).
letter([ዣ],['Z',a]).
letter([ዤ],['Z','E']).
letter([ዥ],['Z','I']).
letter([ዦ],['Z',o]). 

%የ 
letter([የ],[y,e]).
letter([ዩ],[y,u]).
letter([ዪ],[y,i]).
letter([ያ],[y,a]).
letter([ዬ],[y,'E']).
letter([ይ],[y,'I']).
letter([ዮ],[y,o]). 

%ደ 
letter([ደ],[d,e]).
letter([ዱ],[d,u]).
letter([ዲ],[d,i]).
letter([ዳ],[d,a]).
letter([ዴ],[d,'E']).
letter([ድ],[d,'I']).
letter([ዶ],[d,o]). 

%ጀ 
letter([ጀ],[j,e]).
letter([ጁ],[j,u]).
letter([ጂ],[j,i]).
letter([ጃ],[j,a]).
letter([ጄ],[j,'E']).
letter([ጅ],[j,'I']).
letter([ጆ],[j,o]). 

%ገ 
letter([ገ],[g,e]).
letter([ጉ],[g,u]).
letter([ጊ],[g,i]).
letter([ጋ],[g,a]).
letter([ጌ],[g,'E']).
letter([ግ],[g,'I']).
letter([ጎ],[g,o]). 

%ጠ 
letter([ጠ],['T',e]).
letter([ጡ],['T',u]).
letter([ጢ],['T',i]).
letter([ጣ],['T',a]).
letter([ጤ],['T','E']).
letter([ጥ],['T','I']).
letter([ጦ],['T',o]). 

%ጨ 
letter([ጨ],['C',e]).
letter([ጩ],['C',u]).
letter([ጪ],['C',i]).
letter([ጫ],['C',a]).
letter([ጬ],['C','E']).
letter([ጭ],['C','I']).
letter([ጮ],['C',o]). 

%ጰ 
letter([ጰ],['P',e]).
letter([ጱ],['P',u]).
letter([ጲ],['P',i]).
letter([ጳ],['P',a]).
letter([ጴ],['P','E']).
letter([ጵ],['P','I']).
letter([ጶ],['P',o]). 


%ፈ 
letter([ፈ],[f,e]).
letter([ፉ],[f,u]).
letter([ፊ],[f,i]).
letter([ፋ],[f,a]).
letter([ፌ],[f,'E']).
letter([ፍ],[f,'I']).
letter([ፎ],[f,o]). 

%ፐ 
letter([ፐ],[p,e]).
letter([ፑ],[p,u]).
letter([ፒ],[p,i]).
letter([ፓ],[p,a]).
letter([ፔ],[p,'E']).
letter([ፕ],[p,'I']).
letter([ፖ],[p,o]).  
%===========================================================
%ጸ 


%ፀ 


  

