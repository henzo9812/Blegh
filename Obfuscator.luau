local Obf = {}

local b32 = bit32
local schar = string.char
local sbyte = string.byte
local ssub = string.sub
local sfind = string.find
local sformat = string.format
local smatch = string.match
local sgsub = string.gsub
local srep = string.rep
local slen = string.len
local tinsert = table.insert
local tconcat = table.concat
local mfloor = math.floor
local mrandom = math.random
local mabs = math.abs

local KW = {
	["and"]=1,["break"]=1,["do"]=1,["else"]=1,["elseif"]=1,["end"]=1,
	["false"]=1,["for"]=1,["function"]=1,["if"]=1,["in"]=1,["local"]=1,
	["nil"]=1,["not"]=1,["or"]=1,["repeat"]=1,["return"]=1,["then"]=1,
	["true"]=1,["until"]=1,["while"]=1,["continue"]=1,["type"]=1,["export"]=1
}

local BUILTIN = {
	["print"]=1,["warn"]=1,["error"]=1,["assert"]=1,["type"]=1,["typeof"]=1,
	["tostring"]=1,["tonumber"]=1,["select"]=1,["pcall"]=1,["xpcall"]=1,
	["rawget"]=1,["rawset"]=1,["rawequal"]=1,["rawlen"]=1,["unpack"]=1,
	["ipairs"]=1,["pairs"]=1,["next"]=1,["setmetatable"]=1,["getmetatable"]=1,
	["require"]=1,["newproxy"]=1,["gcinfo"]=1,["getfenv"]=1,["setfenv"]=1,
	["math"]=1,["string"]=1,["table"]=1,["bit32"]=1,["coroutine"]=1,
	["os"]=1,["debug"]=1,["utf8"]=1,["buffer"]=1,["vector"]=1,
	["game"]=1,["workspace"]=1,["script"]=1,["Instance"]=1,["Enum"]=1,
	["Color3"]=1,["Vector3"]=1,["Vector2"]=1,["CFrame"]=1,["UDim2"]=1,
	["UDim"]=1,["BrickColor"]=1,["Ray"]=1,["Region3"]=1,["Rect"]=1,
	["TweenInfo"]=1,["NumberSequence"]=1,["ColorSequence"]=1,
	["NumberSequenceKeypoint"]=1,["ColorSequenceKeypoint"]=1,
	["NumberRange"]=1,["PhysicalProperties"]=1,["Faces"]=1,["Axes"]=1,
	["RaycastParams"]=1,["OverlapParams"]=1,["task"]=1,["tick"]=1,
	["time"]=1,["wait"]=1,["delay"]=1,["spawn"]=1,["_G"]=1,["shared"]=1,
	["self"]=1,["true"]=1,["false"]=1,["nil"]=1,
	["loadstring"]=1,["getgenv"]=1,["getrenv"]=1,["hookfunction"]=1
}

local function rInt(a, b) return mrandom(a, b) end

local TK = {
	STR="str",NUM="num",IDENT="id",KW="kw",OP="op",WS="ws",
	CMT="cmt",BOOL="bool",NIL="nil",PUNCT="pn",LONGSTR="ls",
	VARARG="va",INTERP="interp",UNKNOWN="?"
}

local function lex(src)
	local tokens = {}
	local pos = 1
	local len = slen(src)
	local function peek(o) o=o or 0;return ssub(src,pos+o,pos+o) end
	local function peekN(n) return ssub(src,pos,pos+n-1) end
	local function adv(n) n=n or 1;pos=pos+n end
	local function push(tp,val) tinsert(tokens,{t=tp,v=val}) end

	local function readLongStr()
		local lvl=0
		while peek(lvl+1)=="=" do lvl+=1 end
		if peek(lvl+1)~="[" then return nil end
		local start=pos;adv(lvl+2)
		local close="]"..srep("=",lvl).."]"
		local cpos=sfind(src,close,pos,true)
		if not cpos then adv(len-pos+1);return ssub(src,start,len) end
		local result=ssub(src,start,cpos+slen(close)-1)
		pos=cpos+slen(close);return result
	end

	while pos<=len do
		local c=peek()
		local c2=peekN(2)
		if c=="-" and c2=="--" then
			adv(2)
			if peekN(2)=="[[" or(peek()=="[" and peek(1)=="=")then
				local ls=readLongStr()
				if ls then push(TK.CMT,"--"..ls) end
			else
				local s=pos
				while pos<=len and peek()~="\n" do adv() end
				push(TK.CMT,"--"..ssub(src,s,pos-1))
			end
		elseif c=="[" and(peek(1)=="[" or peek(1)=="=")then
			local ls=readLongStr()
			if ls then push(TK.LONGSTR,ls) else push(TK.PUNCT,c);adv() end
		elseif c=='"' or c=="'" then
			local q=c;adv()
			local buf={q}
			while pos<=len do
				local ch=peek()
				if ch=="\\" then tinsert(buf,ch);adv();if pos<=len then tinsert(buf,peek());adv() end
				elseif ch==q then tinsert(buf,ch);adv();break
				else tinsert(buf,ch);adv() end
			end
			push(TK.STR,tconcat(buf))
		elseif c=="`" then
			local buf={c};adv();local depth=0
			while pos<=len do
				local ch=peek()
				if ch=="\\" then tinsert(buf,ch);adv();if pos<=len then tinsert(buf,peek());adv() end
				elseif ch=="{" then depth+=1;tinsert(buf,ch);adv()
				elseif ch=="}" and depth>0 then depth-=1;tinsert(buf,ch);adv()
				elseif ch=="`" then tinsert(buf,ch);adv();break
				else tinsert(buf,ch);adv() end
			end
			push(TK.INTERP,tconcat(buf))
		elseif smatch(c,"%s") then
			local s=pos
			while pos<=len and smatch(peek(),"%s") do adv() end
			push(TK.WS,ssub(src,s,pos-1))
		elseif smatch(c,"[%a_]") then
			local s=pos
			while pos<=len and smatch(peek(),"[%w_]") do adv() end
			local w=ssub(src,s,pos-1)
			if w=="true" or w=="false" then push(TK.BOOL,w)
			elseif w=="nil" then push(TK.NIL,w)
			elseif KW[w] then push(TK.KW,w)
			else push(TK.IDENT,w) end
		elseif smatch(c,"%d") or(c=="." and smatch(peek(1) or "","[%d]"))then
			local s=pos
			if peekN(2)=="0x" or peekN(2)=="0X" then
				adv(2);while pos<=len and smatch(peek(),"[%da-fA-F_]") do adv() end
			elseif peekN(2)=="0b" or peekN(2)=="0B" then
				adv(2);while pos<=len and smatch(peek(),"[01_]") do adv() end
			else
				while pos<=len and smatch(peek(),"[%d_]") do adv() end
				if pos<=len and peek()=="." then adv();while pos<=len and smatch(peek(),"[%d_]") do adv() end end
				if pos<=len and smatch(peek(),"[eE]") then adv();if pos<=len and smatch(peek(),"[%+%-]") then adv() end;while pos<=len and smatch(peek(),"[%d_]") do adv() end end
			end
			push(TK.NUM,ssub(src,s,pos-1))
		elseif c=="." then
			if peekN(3)=="..." then push(TK.VARARG,"...");adv(3)
			elseif peekN(2)==".." then push(TK.OP,"..");adv(2)
			else push(TK.PUNCT,".");adv() end
		else
			local ops3={["..="]=1,["//="]=1}
			local ops2={["=="]=1,["~="]=1,["<="]=1,[">="]=1,["+="]=1,["-="]=1,["*="]=1,["/="]=1,["%="]=1,["^="]=1,["//"] =1,["->"]=1,["::"]=1}
			local tri=peekN(3)
			if ops3[tri] then push(TK.OP,tri);adv(3)
			elseif ops2[c2] then push(TK.OP,c2);adv(2)
			elseif sfind("+-*/%^#<>=(){}[];:,|&?!",c,1,true) then push(TK.OP,c);adv()
			else push(TK.UNKNOWN,c);adv() end
		end
	end
	return tokens
end

local PREFIX_CHARS = {"l","I","O","_"}

local function genName(idx)
	local base=""
	local n=idx
	repeat local r=n%4;base=PREFIX_CHARS[r+1]..base;n=mfloor(n/4) until n==0
	local suffix=""
	local s2=idx*7+3
	for _=1,rInt(2,4) do local r=s2%4;suffix=suffix..PREFIX_CHARS[r+1];s2=mfloor(s2/4)+1 end
	return "_"..base..suffix
end

local function buildScope(tokens)
	local scopes={{}};local depth=1;local nameMap={};local nameIdx=0
	local function curScope() return scopes[depth] end
	local function pushScope() depth+=1;scopes[depth]={} end
	local function popScope() depth=math.max(depth-1,1) end
	local function registerName(o)
		if BUILTIN[o] then return o end
		if nameMap[o] then return nameMap[o] end
		nameIdx+=1;local ob=genName(nameIdx);nameMap[o]=ob;curScope()[o]=ob;return ob
	end
	local function lookupName(o)
		if BUILTIN[o] then return o end
		return nameMap[o]
	end

	local result={};local i=1;local count=#tokens
	local function prevNonWS()
		local j=#result;while j>=1 and result[j].t==TK.WS do j-=1 end
		if j>=1 then return result[j] end;return nil
	end

	while i<=count do
		local tk=tokens[i]
		if tk.t==TK.KW then
			if tk.v=="local" then
				tinsert(result,tk);i+=1
				while i<=count and tokens[i].t==TK.WS do tinsert(result,tokens[i]);i+=1 end
				if i<=count and tokens[i].t==TK.KW and tokens[i].v=="function" then
					tinsert(result,tokens[i]);i+=1
					while i<=count and tokens[i].t==TK.WS do tinsert(result,tokens[i]);i+=1 end
					if i<=count and tokens[i].t==TK.IDENT then
						tinsert(result,{t=TK.IDENT,v=registerName(tokens[i].v)});i+=1
					end
				else
					while i<=count do
						if tokens[i].t==TK.IDENT then tinsert(result,{t=TK.IDENT,v=registerName(tokens[i].v)});i+=1
						elseif tokens[i].t==TK.WS then tinsert(result,tokens[i]);i+=1
						elseif tokens[i].v=="," then tinsert(result,tokens[i]);i+=1
						elseif tokens[i].v==":" then
							tinsert(result,tokens[i]);i+=1
							while i<=count and tokens[i].t==TK.WS do tinsert(result,tokens[i]);i+=1 end
							if i<=count and tokens[i].t==TK.IDENT then tinsert(result,tokens[i]);i+=1 end
						else break end
					end
				end
			elseif tk.v=="for" then
				pushScope();tinsert(result,tk);i+=1
				while i<=count and tokens[i].t==TK.WS do tinsert(result,tokens[i]);i+=1 end
				while i<=count do
					if tokens[i].t==TK.IDENT then tinsert(result,{t=TK.IDENT,v=registerName(tokens[i].v)});i+=1
					elseif tokens[i].t==TK.WS then tinsert(result,tokens[i]);i+=1
					elseif tokens[i].v=="," then tinsert(result,tokens[i]);i+=1
					else break end
				end
			elseif tk.v=="function" then
				tinsert(result,tk);i+=1
				while i<=count and tokens[i].t==TK.WS do tinsert(result,tokens[i]);i+=1 end
				if i<=count and tokens[i].t==TK.IDENT then
					local p=prevNonWS()
					if not(p and p.t==TK.KW and p.v=="local") then
						local lk=lookupName(tokens[i].v)
						if lk then tinsert(result,{t=TK.IDENT,v=lk}) else tinsert(result,tokens[i]) end
						i+=1
						while i<=count and(tokens[i].v=="." or tokens[i].v==":") do
							tinsert(result,tokens[i]);i+=1
							while i<=count and tokens[i].t==TK.WS do tinsert(result,tokens[i]);i+=1 end
							if i<=count and tokens[i].t==TK.IDENT then tinsert(result,tokens[i]);i+=1 end
						end
					end
				end
				pushScope()
				if i<=count and tokens[i].v=="(" then
					tinsert(result,tokens[i]);i+=1
					while i<=count and tokens[i].v~=")" do
						if tokens[i].t==TK.IDENT then tinsert(result,{t=TK.IDENT,v=registerName(tokens[i].v)});i+=1
						elseif tokens[i].v==":" then
							tinsert(result,tokens[i]);i+=1
							while i<=count and tokens[i].t==TK.WS do tinsert(result,tokens[i]);i+=1 end
							if i<=count and tokens[i].t==TK.IDENT then tinsert(result,tokens[i]);i+=1 end
						else tinsert(result,tokens[i]);i+=1 end
					end
				end
			elseif tk.v=="do" or tk.v=="then" or tk.v=="repeat" then
				if tk.v~="do" or not(prevNonWS() and prevNonWS().t==TK.KW and prevNonWS().v=="for") then
					if tk.v~="then" then pushScope() end
				end
				tinsert(result,tk);i+=1
			elseif tk.v=="end" or tk.v=="until" then popScope();tinsert(result,tk);i+=1
			elseif tk.v=="else" or tk.v=="elseif" then popScope();pushScope();tinsert(result,tk);i+=1
			else tinsert(result,tk);i+=1 end
		elseif tk.t==TK.IDENT then
			local lk=lookupName(tk.v)
			tinsert(result,lk and{t=TK.IDENT,v=lk}or tk);i+=1
		else tinsert(result,tk);i+=1 end
	end
	return result
end

local function encNum(n)
	local strats={}
	strats[1]=function()
		local k=rInt(2,97);local shifted=b32.bxor(mfloor(mabs(n)),k)
		if n>=0 and n==mfloor(n) and n<2^31 then return sformat("bit32.bxor(%d,%d)",shifted,k) end;return nil
	end
	strats[2]=function()
		local a=rInt(2,50);local b=rInt(1,200);local target=n*a+b
		if target==mfloor(target) and mabs(target)<2^40 then return sformat("(%s-%d)/%d",tostring(target),b,a) end;return nil
	end
	strats[3]=function()
		if n==mfloor(n) and n>=0 and n<2^32 then
			local hi=b32.rshift(mfloor(n),16);local lo=b32.band(mfloor(n),0xFFFF)
			return sformat("(bit32.lshift(%d,16)+%d)",hi,lo)
		end;return nil
	end
	strats[4]=function() local off=rInt(100,9999);return sformat("(%s+%d-%d)",tostring(n),off,off) end
	strats[5]=function()
		if n==mfloor(n) and n>0 and n<2^31 then
			local k1=rInt(1,255);local k2=rInt(1,255);local v=b32.bxor(b32.bxor(mfloor(n),k1),k2)
			return sformat("bit32.bxor(bit32.bxor(%d,%d),%d)",v,k2,k1)
		end;return nil
	end
	strats[6]=function()
		if n==mfloor(n) and mabs(n)<2^20 then
			local m=rInt(3,13);return sformat("math.floor(%d/%d)",n*m,m)
		end;return nil
	end
	strats[7]=function()
		if n==mfloor(n) and n>=0 and n<2^31 then
			local r=rInt(1,15)
			local rotated=b32.lrotate(mfloor(n),r)
			return sformat("bit32.rrotate(%d,%d)",rotated,r)
		end;return nil
	end
	strats[8]=function()
		if n==mfloor(n) and n>=0 and n<2^20 then
			local a=rInt(2,30);local b=rInt(2,30)
			return sformat("bit32.bxor(bit32.bxor(%d,%d),%d)",b32.bxor(b32.bxor(mfloor(n),a),b),b,a)
		end;return nil
	end
	for _=1,30 do local s=strats[rInt(1,#strats)];local r=s();if r then return r end end
	return tostring(n)
end

local function encStr(raw)
	local q=ssub(raw,1,1);local inner=ssub(raw,2,slen(raw)-1)
	local bytes={};local i=1;local ilen=slen(inner)
	while i<=ilen do
		local ch=ssub(inner,i,i)
		if ch=="\\" and i<ilen then
			local nxt=ssub(inner,i+1,i+1)
			if nxt=="n" then tinsert(bytes,10);i+=2
			elseif nxt=="t" then tinsert(bytes,9);i+=2
			elseif nxt=="r" then tinsert(bytes,13);i+=2
			elseif nxt=="\\" then tinsert(bytes,92);i+=2
			elseif nxt==q then tinsert(bytes,sbyte(q));i+=2
			elseif nxt=="0" then tinsert(bytes,0);i+=2
			elseif nxt=="a" then tinsert(bytes,7);i+=2
			elseif nxt=="b" then tinsert(bytes,8);i+=2
			elseif nxt=="f" then tinsert(bytes,12);i+=2
			elseif nxt=="v" then tinsert(bytes,11);i+=2
			elseif smatch(nxt,"%d") then
				local ds=smatch(ssub(inner,i+1,i+3),"^(%d%d?%d?)");tinsert(bytes,tonumber(ds));i+=1+slen(ds)
			elseif nxt=="x" then
				local hx=ssub(inner,i+2,i+3);tinsert(bytes,tonumber(hx,16) or 0);i+=4
			else tinsert(bytes,sbyte(nxt));i+=2 end
		else tinsert(bytes,sbyte(ch));i+=1 end
	end
	if #bytes==0 then return '""' end

	local keyLen=rInt(5,12)
	local key={};for idx=1,keyLen do key[idx]=rInt(1,254) end
	local enc={};for idx=1,#bytes do
		local ki=((idx-1)%keyLen)+1
		enc[idx]=b32.bxor(bytes[idx],key[ki])
	end

	local method=rInt(1,3)
	local kStr="{"..tconcat(key,",").."}"
	local dStr="{"..tconcat(enc,",").."}"

	if method==1 then
		return sformat(
			"(function(k,d)local b=buffer.create(#d)for i=1,#d do buffer.writeu8(b,i-1,bit32.bxor(d[i],k[((i-1)%%#k)+1]))end return buffer.readstring(b,0,#d)end)(%s,%s)",
			kStr,dStr)
	elseif method==2 then
		return sformat(
			"(function(k,d)local t=table.create(#d)for i=1,#d do t[i]=string.char(bit32.bxor(d[i],k[((i-1)%%#k)+1]))end return table.concat(t)end)(%s,%s)",
			kStr,dStr)
	else
		return sformat(
			"(function(k,d)local r=\"\"for i=1,#d do r=r..string.char(bit32.bxor(d[i],k[((i-1)%%#k)+1]))end return r end)(%s,%s)",
			kStr,dStr)
	end
end

local function encBool(v)
	local strats={}
	strats[1]=function() if v=="true" then local a=rInt(1,500);return sformat("(bit32.band(%d,%d)==%d)",a,a,a) else local a=rInt(1,500);local b=rInt(501,999);return sformat("(bit32.band(%d,%d)==%d)",a,b,a+b+1) end end
	strats[2]=function() if v=="true" then local x=rInt(1,999);return sformat("(bit32.bxor(%d,%d)==0)",x,x) else local x=rInt(1,999);return sformat("(bit32.bxor(%d,%d)==0)",x,x+1) end end
	strats[3]=function() if v=="true" then local a=rInt(2,50);return sformat("(math.floor(%d/%d)==%d)",a*a,a,a) else local a=rInt(2,50);return sformat("(math.floor(%d/%d)==%d)",a*a,a,a+1) end end
	strats[4]=function() if v=="true" then return sformat("(%d>%d)",rInt(50,999),rInt(1,49)) else return sformat("(%d>%d)",rInt(1,49),rInt(50,999)) end end
	strats[5]=function() if v=="true" then local x=rInt(1,200);return sformat("(bit32.lshift(1,%d)==%d)",x%31,b32.lshift(1,x%31)) else local x=rInt(1,200);return sformat("(bit32.lshift(1,%d)==%d)",x%31,b32.lshift(1,x%31)+1) end end
	return strats[rInt(1,#strats)]()
end

local function encNil()
	local s={{function() return"({})[" ..rInt(2,999).."]" end},{function() return"(select("..rInt(2,5)..",(function()end)()))" end},{function() return sformat("(rawget({%d},%d))",rInt(100,9999),rInt(5,20)) end}}
	return s[rInt(1,#s)][1]()
end

local function transform(tokens,cfg)
	local out={}
	local function nextNonWS(from)
		for j=from,#tokens do if tokens[j].t~=TK.WS and tokens[j].t~=TK.CMT then return tokens[j] end end;return nil
	end
	local function prevOutNonWS()
		for j=#out,1,-1 do if out[j].t~=TK.WS then return out[j] end end;return nil
	end
	local function needsSpace(a,b)
		if not a or not b then return false end
		local aw=(a.t==TK.KW or a.t==TK.IDENT or a.t==TK.BOOL or a.t==TK.NIL or a.t==TK.NUM or a.t==TK.VARARG)
		local bw=(b.t==TK.KW or b.t==TK.IDENT or b.t==TK.BOOL or b.t==TK.NIL or b.t==TK.NUM or b.t==TK.VARARG)
		return aw and bw
	end
	for i=1,#tokens do
		local tk=tokens[i]
		if tk.t==TK.CMT then
		elseif tk.t==TK.WS then
			local prev=prevOutNonWS();local nxt=nextNonWS(i+1)
			if sfind(tk.v,"\n") then tinsert(out,{t=TK.WS,v="\n"})
			elseif needsSpace(prev,nxt) then tinsert(out,{t=TK.WS,v=" "}) end
		elseif tk.t==TK.STR and cfg.encStr then
			tinsert(out,{t=TK.STR,v=encStr(tk.v),raw=true})
		elseif tk.t==TK.LONGSTR and cfg.encStr then
			local inner=tk.v;local content=""
			local _,eqEnd=smatch(inner,"^%[(%=*)%[")
			if eqEnd then
				local lvl=slen(eqEnd or "");local open="%["..srep("=",lvl).."%[";local close="%]"..srep("=",lvl).."%]"
				content=smatch(inner,open.."(.-)"..close) or ""
			else content=smatch(inner,"^%[%[(.-)%]%]") or "" end
			if ssub(content,1,1)=="\n" then content=ssub(content,2) end
			local fakeStr='"'
			for ci=1,slen(content) do
				local ch=ssub(content,ci,ci)
				if ch=='"' then fakeStr=fakeStr..'\\"'
				elseif ch=="\\" then fakeStr=fakeStr.."\\\\"
				elseif ch=="\n" then fakeStr=fakeStr.."\\n"
				elseif ch=="\r" then fakeStr=fakeStr.."\\r"
				elseif ch=="\t" then fakeStr=fakeStr.."\\t"
				elseif ch=="\0" then fakeStr=fakeStr.."\\0"
				else fakeStr=fakeStr..ch end
			end
			fakeStr=fakeStr..'"'
			tinsert(out,{t=TK.STR,v=encStr(fakeStr),raw=true})
		elseif tk.t==TK.NUM and cfg.encNum then
			local cleaned=(sgsub(tk.v,"_",""));local nVal=tonumber(cleaned)
			if nVal and mabs(nVal)<2^31 and nVal==mfloor(nVal) and nVal>=0 then
				tinsert(out,{t=TK.NUM,v="("..encNum(nVal)..")",raw=true})
			else tinsert(out,tk) end
		elseif tk.t==TK.BOOL and cfg.encBool then
			tinsert(out,{t=TK.BOOL,v=encBool(tk.v),raw=true})
		elseif tk.t==TK.NIL and cfg.encNil then
			tinsert(out,{t=TK.NIL,v=encNil(),raw=true})
		else tinsert(out,tk) end
	end
	return out
end

local function emit(tokens)
	local p={};for _,tk in ipairs(tokens) do tinsert(p,tk.v) end;return tconcat(p)
end

local function genJunk()
	local s={}
	s[1]=function() local vn=genName(rInt(9000,9999));return sformat("if bit32.bxor(%d,%d)==0 then local %s=%d end",rInt(1,999),rInt(1,999),vn,rInt(0,100)) end
	s[2]=function() local vn=genName(rInt(8000,8999));local x=rInt(2,50);return sformat("local %s=bit32.band(%d,bit32.bnot(%d))",vn,x,x) end
	s[3]=function() local vn=genName(rInt(7000,7999));return sformat("local %s=(function()local _=0 for _i=1,%d do _=bit32.bxor(_,_i)end return _ end)()",vn,rInt(1,200)) end
	s[4]=function() local vn=genName(rInt(6000,6999));return sformat("do local %s=math.floor(math.sin(%d)*%d)end",vn,rInt(1,100),rInt(10,1000)) end
	s[5]=function() local vn=genName(rInt(5000,5999));local a,b=rInt(1,50),rInt(1,50);return sformat("local %s=bit32.rshift(bit32.lshift(%d,%d),%d)",vn,a,b,b) end
	return s[rInt(1,#s)]()
end

local function injectJunk(code,chance)
	local lines={};local cur=""
	for i=1,slen(code) do
		local ch=ssub(code,i,i)
		if ch=="\n" then tinsert(lines,cur);cur="" else cur=cur..ch end
	end
	if slen(cur)>0 then tinsert(lines,cur) end
	local result={}
	for idx=1,#lines do
		tinsert(result,lines[idx])
		local trimmed=sgsub(lines[idx],"^%s+","")
		if smatch(trimmed,"^return") or smatch(trimmed,"^break") or smatch(trimmed,"^continue") then continue end
		local nxt=lines[idx+1];if not nxt then continue end
		local nxtT=sgsub(nxt,"^%s+","")
		if smatch(nxtT,"^end") or smatch(nxtT,"^else") or smatch(nxtT,"^elseif") or smatch(nxtT,"^until") then continue end
		if mrandom()<chance then
			if smatch(trimmed,"^end") or smatch(trimmed,"%)$") or smatch(trimmed,"%w$") then
				tinsert(result,genJunk())
			elseif smatch(nxtT,"^local%s") or smatch(nxtT,"^for%s") or smatch(nxtT,"^if%s") or smatch(nxtT,"^while%s") or smatch(nxtT,"^%w") then
				tinsert(result,genJunk())
			end
		end
	end
	return tconcat(result,"\n")
end

local function streamCipherEncrypt(data, seeds)
	local s0 = seeds[1]
	local s1 = seeds[2]
	local s2 = seeds[3]
	local encrypted = {}
	for i = 1, #data do
		s0 = b32.band(s0 * 214013 + 2531011, 0xFFFFFFFF)
		s1 = b32.bxor(s1, b32.lrotate(s0, 13))
		s2 = b32.band(s2 + b32.rshift(s0, 16), 0xFFFFFFFF)
		local keyByte = b32.band(b32.bxor(b32.rshift(s0, 16), b32.band(s1, 0xFF), b32.band(s2, 0xFF)), 0xFF)
		encrypted[i] = b32.bxor(data[i], keyByte)
	end
	return encrypted
end

local function sourceToBytes(src)
	local bytes = {}
	for i = 1, slen(src) do
		tinsert(bytes, sbyte(src, i))
	end
	return bytes
end

local function scatterData(encrypted, numChunks)
	local chunks = {}
	for i = 1, numChunks do chunks[i] = {} end
	for i = 1, #encrypted do
		local ci = ((i - 1) % numChunks) + 1
		tinsert(chunks[ci], encrypted[i])
	end
	return chunks
end

local function genVarName()
	local len = rInt(6, 12)
	local chars = {"_", "l", "I", "O"}
	local buf = {"_"}
	for i = 2, len do
		tinsert(buf, chars[rInt(1, #chars)])
	end
	return tconcat(buf)
end

local function genOpaqueTrue()
	local strats = {}
	strats[1] = function()
		local a = rInt(100, 999)
		return sformat("(bit32.band(%d,1)==0)", a * 2)
	end
	strats[2] = function()
		local x = rInt(1, 2^15)
		local r = rInt(1, 30)
		return sformat("(bit32.rrotate(bit32.lrotate(%d,%d),%d)==%d)", x, r, r, x)
	end
	strats[3] = function()
		local a = rInt(2, 50)
		return sformat("(math.floor(%d/%d)==%d)", a * a, a, a)
	end
	strats[4] = function()
		local x = rInt(1, 999)
		return sformat("(bit32.bxor(%d,%d)==0)", x, x)
	end
	return strats[rInt(1, #strats)]()
end

local function buildDecoder(chunks, seeds, totalLen, numChunks)
	local vS0 = genVarName()
	local vS1 = genVarName()
	local vS2 = genVarName()
	local vBuf = genVarName()
	local vI = genVarName()
	local vK = genVarName()
	local vEnc = genVarName()
	local vIdx = genVarName()
	local vJ = genVarName()
	local vResult = genVarName()
	local vChunks = {}
	for i = 1, numChunks do vChunks[i] = genVarName() end

	local lines = {}

	for i = 1, numChunks do
		tinsert(lines, sformat("local %s={%s}", vChunks[i], tconcat(chunks[i], ",")))
	end

	tinsert(lines, sformat("local %s=table.create(%d)", vEnc, totalLen))
	tinsert(lines, sformat("local %s=1", vIdx))
	tinsert(lines, sformat("for %s=1,#%s do", vI, vChunks[1]))
	for ci = 1, numChunks do
		tinsert(lines, sformat("if %s<=%d and %s[%s] then %s[%s]=%s[%s] %s=%s+1 end",
			vIdx, totalLen, vChunks[ci], vI, vEnc, vIdx, vChunks[ci], vI, vIdx, vIdx))
	end
	tinsert(lines, "end")

	tinsert(lines, sformat("local %s=%d", vS0, seeds[1]))
	tinsert(lines, sformat("local %s=%d", vS1, seeds[2]))
	tinsert(lines, sformat("local %s=%d", vS2, seeds[3]))
	tinsert(lines, sformat("local %s=buffer.create(%d)", vBuf, totalLen))

	tinsert(lines, sformat("for %s=1,%d do", vI, totalLen))
	tinsert(lines, sformat("%s=bit32.band(%s*214013+2531011,0xFFFFFFFF)", vS0, vS0))
	tinsert(lines, sformat("%s=bit32.bxor(%s,bit32.lrotate(%s,13))", vS1, vS1, vS0))
	tinsert(lines, sformat("%s=bit32.band(%s+bit32.rshift(%s,16),0xFFFFFFFF)", vS2, vS2, vS0))
	tinsert(lines, sformat("local %s=bit32.band(bit32.bxor(bit32.rshift(%s,16),bit32.band(%s,0xFF),bit32.band(%s,0xFF)),0xFF)",
		vK, vS0, vS1, vS2))
	tinsert(lines, sformat("buffer.writeu8(%s,%s-1,bit32.bxor(%s[%s] or 0,%s))", vBuf, vI, vEnc, vI, vK))
	tinsert(lines, "end")

	tinsert(lines, sformat("local %s=buffer.readstring(%s,0,%d)", vResult, vBuf, totalLen))

	tinsert(lines, sformat("if %s then", genOpaqueTrue()))
	tinsert(lines, sformat("loadstring(%s)()", vResult))
	tinsert(lines, "else")
	local vDummy = genVarName()
	tinsert(lines, sformat("local %s=%d", vDummy, rInt(1, 99999)))
	tinsert(lines, "end")

	return tconcat(lines, "\n")
end

local function wrapInLoader(code)
	local bytes = sourceToBytes(code)
	local totalLen = #bytes
	local numChunks = rInt(3, 6)
	local seeds = {rInt(1, 0xFFFFFF), rInt(1, 0xFFFFFF), rInt(1, 0xFFFFFF)}

	local encrypted = streamCipherEncrypt(bytes, {seeds[1], seeds[2], seeds[3]})
	local chunks = scatterData(encrypted, numChunks)

	return buildDecoder(chunks, seeds, totalLen, numChunks)
end

local function addProxyLayer(code)
	local proxies = {}
	local pBxor = genVarName()
	local pBand = genVarName()
	local pBor = genVarName()
	local pLshift = genVarName()
	local pRshift = genVarName()
	local pLrot = genVarName()
	local pRrot = genVarName()
	local pFloor = genVarName()
	local pChar = genVarName()
	local pByte = genVarName()
	local pSub = genVarName()
	local pBnot = genVarName()

	local header = sformat(
		"local %s=bit32.bxor local %s=bit32.band local %s=bit32.bor local %s=bit32.lshift local %s=bit32.rshift local %s=bit32.lrotate local %s=bit32.rrotate local %s=math.floor local %s=string.char local %s=string.byte local %s=string.sub local %s=bit32.bnot\n",
		pBxor, pBand, pBor, pLshift, pRshift, pLrot, pRrot, pFloor, pChar, pByte, pSub, pBnot
	)

	code = sgsub(code, "bit32%.bxor", pBxor)
	code = sgsub(code, "bit32%.band", pBand)
	code = sgsub(code, "bit32%.bor", pBor)
	code = sgsub(code, "bit32%.lshift", pLshift)
	code = sgsub(code, "bit32%.rshift", pRshift)
	code = sgsub(code, "bit32%.lrotate", pLrot)
	code = sgsub(code, "bit32%.rrotate", pRrot)
	code = sgsub(code, "bit32%.bnot", pBnot)
	code = sgsub(code, "math%.floor", pFloor)
	code = sgsub(code, "string%.char", pChar)
	code = sgsub(code, "string%.byte", pByte)
	code = sgsub(code, "string%.sub", pSub)

	return header .. code
end

local DEFAULT_CFG = {
	encStr = true,
	encNum = true,
	encBool = true,
	encNil = true,
	renameVars = true,
	junk = true,
	junkChance = 0.10,
	seed = nil,
	layers = 2,
	scatter = true,
	proxy = true,
}

function Obf.obfuscate(source: string, config: {[string]: any}?): string
	local cfg = {}
	for k, v in pairs(DEFAULT_CFG) do cfg[k] = v end
	if config then for k, v in pairs(config) do cfg[k] = v end end

	math.randomseed(cfg.seed or os.clock() * 1000)

	local tokens = lex(source)
	if cfg.renameVars then tokens = buildScope(tokens) end
	tokens = transform(tokens, cfg)
	local code = emit(tokens)

	if cfg.junk then
		code = injectJunk(code, cfg.junkChance or 0.10)
	end

	for layer = 1, (cfg.layers or 2) do
		code = wrapInLoader(code)
		if cfg.proxy then
			code = addProxyLayer(code)
		end
		if cfg.junk and layer < (cfg.layers or 2) then
			code = injectJunk(code, cfg.junkChance or 0.10)
		end
	end

	return code
end

function Obf.obfuscateLight(source: string): string
	return Obf.obfuscate(source, {
		encStr=true,encNum=false,encBool=true,encNil=false,
		renameVars=true,junk=false,layers=1,proxy=true
	})
end

function Obf.obfuscateHeavy(source: string): string
	return Obf.obfuscate(source, {
		encStr=true,encNum=true,encBool=true,encNil=true,
		renameVars=true,junk=true,junkChance=0.20,layers=3,proxy=true
	})
end

return Obf
