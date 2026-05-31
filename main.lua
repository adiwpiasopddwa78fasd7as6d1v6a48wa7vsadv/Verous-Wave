--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.9) ~  Much Love, Ferib 

]]--

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 213) then
					if (Enum <= 106) then
						if (Enum <= 52) then
							if (Enum <= 25) then
								if (Enum <= 12) then
									if (Enum <= 5) then
										if (Enum <= 2) then
											if (Enum <= 0) then
												local B;
												local A;
												Stk[Inst[2]] = Env[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												B = Stk[Inst[3]];
												Stk[A + 1] = B;
												Stk[A] = B[Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												if not Stk[Inst[2]] then
													VIP = VIP + 1;
												else
													VIP = Inst[3];
												end
											elseif (Enum > 1) then
												Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3] ~= 0;
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												for Idx = Inst[2], Inst[3] do
													Stk[Idx] = nil;
												end
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											else
												local Results;
												local Edx;
												local Results, Limit;
												local B;
												local A;
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												B = Stk[Inst[3]];
												Stk[A + 1] = B;
												Stk[A] = B[Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Results, Limit = _R(Stk[A](Stk[A + 1]));
												Top = (Limit + A) - 1;
												Edx = 0;
												for Idx = A, Top do
													Edx = Edx + 1;
													Stk[Idx] = Results[Edx];
												end
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Results = {Stk[A](Unpack(Stk, A + 1, Top))};
												Edx = 0;
												for Idx = A, Inst[4] do
													Edx = Edx + 1;
													Stk[Idx] = Results[Edx];
												end
												VIP = VIP + 1;
												Inst = Instr[VIP];
												VIP = Inst[3];
											end
										elseif (Enum <= 3) then
											local B;
											local A;
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										elseif (Enum > 4) then
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											VIP = Inst[3];
										else
											local Edx;
											local Results;
											local B;
											local A;
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] ^ Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Results = {Stk[A](Stk[A + 1])};
											Edx = 0;
											for Idx = A, Inst[4] do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if (Inst[2] <= Stk[Inst[4]]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 8) then
										if (Enum <= 6) then
											local B;
											local A;
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Stk[Inst[4]]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
										elseif (Enum > 7) then
											local B;
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
										else
											local A;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if not Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 10) then
										if (Enum == 9) then
											local B;
											local A;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										else
											local Edx;
											local Results;
											local A;
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Results = {Stk[A](Stk[A + 1])};
											Edx = 0;
											for Idx = A, Inst[4] do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											VIP = Inst[3];
										end
									elseif (Enum > 11) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									else
										local Edx;
										local Results, Limit;
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									end
								elseif (Enum <= 18) then
									if (Enum <= 15) then
										if (Enum <= 13) then
											local B;
											local A;
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
										elseif (Enum > 14) then
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										else
											local B;
											local A;
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											for Idx = Inst[2], Inst[3] do
												Stk[Idx] = nil;
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										end
									elseif (Enum <= 16) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 17) then
										local B;
										local T;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										T = Stk[A];
										B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									else
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								elseif (Enum <= 21) then
									if (Enum <= 19) then
										Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
									elseif (Enum == 20) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local Edx;
										local Results;
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 23) then
									if (Enum > 22) then
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									else
										local B;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									end
								elseif (Enum == 24) then
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
								else
									local B;
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 38) then
								if (Enum <= 31) then
									if (Enum <= 28) then
										if (Enum <= 26) then
											local A;
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											for Idx = Inst[2], Inst[3] do
												Stk[Idx] = nil;
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										elseif (Enum == 27) then
											local B;
											local A;
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										else
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 29) then
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum == 30) then
										local B;
										local T;
										local A;
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										T = Stk[A];
										B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									else
										local B;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 34) then
									if (Enum <= 32) then
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum == 33) then
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									else
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 36) then
									if (Enum > 35) then
										local A = Inst[2];
										do
											return Stk[A], Stk[A + 1];
										end
									else
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum > 37) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local B;
									local A;
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum <= 45) then
								if (Enum <= 41) then
									if (Enum <= 39) then
										local A;
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									elseif (Enum == 40) then
										local B;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local B;
										local A;
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									end
								elseif (Enum <= 43) then
									if (Enum == 42) then
										local B;
										local A;
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
									else
										Stk[Inst[2]]();
									end
								elseif (Enum > 44) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								elseif (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 48) then
								if (Enum <= 46) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
								elseif (Enum == 47) then
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 50) then
								if (Enum == 49) then
									local B;
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum == 51) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local K;
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 79) then
							if (Enum <= 65) then
								if (Enum <= 58) then
									if (Enum <= 55) then
										if (Enum <= 53) then
											local B;
											local T;
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = -Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											T = Stk[A];
											B = Inst[3];
											for Idx = 1, B do
												T[Idx] = Stk[A + Idx];
											end
										elseif (Enum > 54) then
											local A = Inst[2];
											do
												return Stk[A](Unpack(Stk, A + 1, Top));
											end
										else
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											VIP = Inst[3];
										end
									elseif (Enum <= 56) then
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
									elseif (Enum == 57) then
										if (Stk[Inst[2]] <= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Upvalues[Inst[3]];
									end
								elseif (Enum <= 61) then
									if (Enum <= 59) then
										local A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									elseif (Enum > 60) then
										local B;
										local A;
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									else
										local A;
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 63) then
									if (Enum > 62) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									else
										Stk[Inst[2]] = -Stk[Inst[3]];
									end
								elseif (Enum == 64) then
									local B;
									local A;
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 72) then
								if (Enum <= 68) then
									if (Enum <= 66) then
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									elseif (Enum > 67) then
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									end
								elseif (Enum <= 70) then
									if (Enum == 69) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local Results;
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum == 71) then
									local B;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 75) then
								if (Enum <= 73) then
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum == 74) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local B;
									local A;
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum <= 77) then
								if (Enum > 76) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum > 78) then
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 92) then
							if (Enum <= 85) then
								if (Enum <= 82) then
									if (Enum <= 80) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									elseif (Enum > 81) then
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local Results;
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 83) then
									if (Stk[Inst[2]] < Inst[4]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								elseif (Enum > 84) then
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 88) then
								if (Enum <= 86) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								elseif (Enum > 87) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 90) then
								if (Enum > 89) then
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								end
							elseif (Enum == 91) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 99) then
							if (Enum <= 95) then
								if (Enum <= 93) then
									if (Inst[2] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 94) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Inst[2] < Stk[Inst[4]]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							elseif (Enum <= 97) then
								if (Enum == 96) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum > 98) then
								local VA;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Top = (A + Varargsz) - 1;
								for Idx = A, Top do
									VA = Vararg[Idx - A];
									Stk[Idx] = VA;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Top));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							end
						elseif (Enum <= 102) then
							if (Enum <= 100) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
							elseif (Enum > 101) then
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								local K;
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 104) then
							if (Enum == 103) then
								local B;
								local T;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum == 105) then
							local A;
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 159) then
						if (Enum <= 132) then
							if (Enum <= 119) then
								if (Enum <= 112) then
									if (Enum <= 109) then
										if (Enum <= 107) then
											local B;
											local A;
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
										elseif (Enum > 108) then
											Stk[Inst[2]] = Inst[3] - Stk[Inst[4]];
										else
											local B;
											local A;
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										end
									elseif (Enum <= 110) then
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									elseif (Enum > 111) then
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									else
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								elseif (Enum <= 115) then
									if (Enum <= 113) then
										Stk[Inst[2]] = Inst[3] ~= 0;
									elseif (Enum == 114) then
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									else
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 117) then
									if (Enum == 116) then
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum > 118) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 125) then
								if (Enum <= 122) then
									if (Enum <= 120) then
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 121) then
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										local NewProto = Proto[Inst[3]];
										local NewUvals;
										local Indexes = {};
										NewUvals = Setmetatable({}, {__index=function(_, Key)
											local Val = Indexes[Key];
											return Val[1][Val[2]];
										end,__newindex=function(_, Key, Value)
											local Val = Indexes[Key];
											Val[1][Val[2]] = Value;
										end});
										for Idx = 1, Inst[4] do
											VIP = VIP + 1;
											local Mvm = Instr[VIP];
											if (Mvm[1] == 386) then
												Indexes[Idx - 1] = {Stk,Mvm[3]};
											else
												Indexes[Idx - 1] = {Upvalues,Mvm[3]};
											end
											Lupvals[#Lupvals + 1] = Indexes;
										end
										Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
									end
								elseif (Enum <= 123) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								elseif (Enum > 124) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 128) then
								if (Enum <= 126) then
									local Edx;
									local Results, Limit;
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A]());
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								elseif (Enum > 127) then
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 130) then
								if (Enum == 129) then
									Stk[Inst[2]] = {};
								else
									local B;
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum > 131) then
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
							else
								local B;
								local A;
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 145) then
							if (Enum <= 138) then
								if (Enum <= 135) then
									if (Enum <= 133) then
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 134) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local A;
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									end
								elseif (Enum <= 136) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								elseif (Enum == 137) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 141) then
								if (Enum <= 139) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 140) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum <= 143) then
								if (Enum == 142) then
									local B;
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local Step;
									local Index;
									local A;
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Index = Stk[A];
									Step = Stk[A + 2];
									if (Step > 0) then
										if (Index > Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Index < Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								end
							elseif (Enum > 144) then
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 152) then
							if (Enum <= 148) then
								if (Enum <= 146) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum == 147) then
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local B;
									local A;
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 150) then
								if (Enum > 149) then
									local Step;
									local Index;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Index = Stk[A];
									Step = Stk[A + 2];
									if (Step > 0) then
										if (Index > Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Index < Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								else
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum > 151) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 155) then
							if (Enum <= 153) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 154) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 157) then
							if (Enum == 156) then
								local A;
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum == 158) then
							local B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 186) then
						if (Enum <= 172) then
							if (Enum <= 165) then
								if (Enum <= 162) then
									if (Enum <= 160) then
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum == 161) then
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									end
								elseif (Enum <= 163) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								elseif (Enum == 164) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 168) then
								if (Enum <= 166) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								elseif (Enum > 167) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									do
										return Stk[Inst[2]]();
									end
								end
							elseif (Enum <= 170) then
								if (Enum == 169) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum == 171) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 179) then
							if (Enum <= 175) then
								if (Enum <= 173) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								elseif (Enum == 174) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 177) then
								if (Enum == 176) then
									local K;
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum == 178) then
								local B;
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 182) then
							if (Enum <= 180) then
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 181) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							end
						elseif (Enum <= 184) then
							if (Enum > 183) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 185) then
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							do
								return;
							end
						end
					elseif (Enum <= 199) then
						if (Enum <= 192) then
							if (Enum <= 189) then
								if (Enum <= 187) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								elseif (Enum > 188) then
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 190) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum > 191) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 195) then
							if (Enum <= 193) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum > 194) then
								local K;
								local B;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								Stk[Inst[2]] = not Stk[Inst[3]];
							end
						elseif (Enum <= 197) then
							if (Enum == 196) then
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 198) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 206) then
						if (Enum <= 202) then
							if (Enum <= 200) then
								local T;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								for Idx = A + 1, Top do
									Insert(T, Stk[Idx]);
								end
							elseif (Enum == 201) then
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 204) then
							if (Enum > 203) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum > 205) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							local A = Inst[2];
							local Index = Stk[A];
							local Step = Stk[A + 2];
							if (Step > 0) then
								if (Index > Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							elseif (Index < Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						end
					elseif (Enum <= 209) then
						if (Enum <= 207) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 208) then
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 211) then
						if (Enum > 210) then
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = not Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum > 212) then
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						local B;
						local A;
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 320) then
					if (Enum <= 266) then
						if (Enum <= 239) then
							if (Enum <= 226) then
								if (Enum <= 219) then
									if (Enum <= 216) then
										if (Enum <= 214) then
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										elseif (Enum > 215) then
											local B;
											local A;
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
										else
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
										end
									elseif (Enum <= 217) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									elseif (Enum == 218) then
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									else
										local B;
										local A;
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									end
								elseif (Enum <= 222) then
									if (Enum <= 220) then
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									elseif (Enum == 221) then
										do
											return Stk[Inst[2]];
										end
									else
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 224) then
									if (Enum == 223) then
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									else
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									end
								elseif (Enum > 225) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 232) then
								if (Enum <= 229) then
									if (Enum <= 227) then
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 228) then
										local B;
										local A;
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									else
										local B;
										local T;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										T = Stk[A];
										B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									end
								elseif (Enum <= 230) then
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								elseif (Enum > 231) then
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 235) then
								if (Enum <= 233) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								elseif (Enum == 234) then
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 237) then
								if (Enum == 236) then
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum == 238) then
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 252) then
							if (Enum <= 245) then
								if (Enum <= 242) then
									if (Enum <= 240) then
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									elseif (Enum == 241) then
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									end
								elseif (Enum <= 243) then
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								elseif (Enum > 244) then
									local A = Inst[2];
									local Step = Stk[A + 2];
									local Index = Stk[A] + Step;
									Stk[A] = Index;
									if (Step > 0) then
										if (Index <= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									elseif (Index >= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								else
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 248) then
								if (Enum <= 246) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum > 247) then
									local B;
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 250) then
								if (Enum == 249) then
									local B;
									local A;
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum == 251) then
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 259) then
							if (Enum <= 255) then
								if (Enum <= 253) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum > 254) then
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local A;
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 257) then
								if (Enum == 256) then
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								else
									local T;
									local K;
									local B;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum == 258) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 262) then
							if (Enum <= 260) then
								local A;
								local K;
								local B;
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum == 261) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Stk[Inst[2]] < Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 264) then
							if (Enum == 263) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum == 265) then
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local Edx;
							local Results;
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 293) then
						if (Enum <= 279) then
							if (Enum <= 272) then
								if (Enum <= 269) then
									if (Enum <= 267) then
										local B;
										local A;
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum == 268) then
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									else
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 270) then
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum > 271) then
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 275) then
								if (Enum <= 273) then
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum == 274) then
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Inst[3] do
										Insert(T, Stk[Idx]);
									end
								else
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 277) then
								if (Enum == 276) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum == 278) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 286) then
							if (Enum <= 282) then
								if (Enum <= 280) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 281) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 284) then
								if (Enum == 283) then
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum > 285) then
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 289) then
							if (Enum <= 287) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							elseif (Enum > 288) then
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 291) then
							if (Enum == 290) then
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum == 292) then
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						end
					elseif (Enum <= 306) then
						if (Enum <= 299) then
							if (Enum <= 296) then
								if (Enum <= 294) then
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								elseif (Enum > 295) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 297) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Enum == 298) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Top do
									Insert(T, Stk[Idx]);
								end
							else
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 302) then
							if (Enum <= 300) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Enum > 301) then
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A = Inst[2];
								Top = (A + Varargsz) - 1;
								for Idx = A, Top do
									local VA = Vararg[Idx - A];
									Stk[Idx] = VA;
								end
							end
						elseif (Enum <= 304) then
							if (Enum > 303) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum == 305) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						end
					elseif (Enum <= 313) then
						if (Enum <= 309) then
							if (Enum <= 307) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Enum == 308) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 311) then
							if (Enum == 310) then
								local B;
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum > 312) then
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local B;
							local A;
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 316) then
						if (Enum <= 314) then
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
						elseif (Enum == 315) then
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						else
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 318) then
						if (Enum == 317) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum == 319) then
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
					else
						local B;
						local T;
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						T = Stk[A];
						B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					end
				elseif (Enum <= 374) then
					if (Enum <= 347) then
						if (Enum <= 333) then
							if (Enum <= 326) then
								if (Enum <= 323) then
									if (Enum <= 321) then
										local K;
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									elseif (Enum == 322) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									end
								elseif (Enum <= 324) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								elseif (Enum == 325) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local A;
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum <= 329) then
								if (Enum <= 327) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								elseif (Enum > 328) then
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
								else
									local A = Inst[2];
									local C = Inst[4];
									local CB = A + 2;
									local Result = {Stk[A](Stk[A + 1], Stk[CB])};
									for Idx = 1, C do
										Stk[CB + Idx] = Result[Idx];
									end
									local R = Result[1];
									if R then
										Stk[CB] = R;
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								end
							elseif (Enum <= 331) then
								if (Enum > 330) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
								else
									Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
								end
							elseif (Enum > 332) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 340) then
							if (Enum <= 336) then
								if (Enum <= 334) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 335) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 338) then
								if (Enum == 337) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum == 339) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							elseif (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 343) then
							if (Enum <= 341) then
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 342) then
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 345) then
							if (Enum == 344) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum == 346) then
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						else
							local B;
							local T;
							local A;
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 360) then
						if (Enum <= 353) then
							if (Enum <= 350) then
								if (Enum <= 348) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								elseif (Enum > 349) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 351) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							elseif (Enum > 352) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 356) then
							if (Enum <= 354) then
								local B;
								local A;
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							elseif (Enum > 355) then
								Stk[Inst[2]] = Stk[Inst[3]] ^ Inst[4];
							else
								local B;
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 358) then
							if (Enum == 357) then
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							else
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 359) then
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
						else
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 367) then
						if (Enum <= 363) then
							if (Enum <= 361) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 362) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 365) then
							if (Enum > 364) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum == 366) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 370) then
						if (Enum <= 368) then
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 369) then
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 372) then
						if (Enum > 371) then
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum > 373) then
						local B;
						local A;
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					else
						local B;
						local A;
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					end
				elseif (Enum <= 401) then
					if (Enum <= 387) then
						if (Enum <= 380) then
							if (Enum <= 377) then
								if (Enum <= 375) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								elseif (Enum == 376) then
									local T;
									local VA;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Top = (A + Varargsz) - 1;
									for Idx = A, Top do
										VA = Vararg[Idx - A];
										Stk[Idx] = VA;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									for Idx = A + 1, Top do
										Insert(T, Stk[Idx]);
									end
								else
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 378) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Enum == 379) then
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 383) then
							if (Enum <= 381) then
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							elseif (Enum > 382) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 385) then
							if (Enum > 384) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local A = Inst[2];
								local Cls = {};
								for Idx = 1, #Lupvals do
									local List = Lupvals[Idx];
									for Idz = 0, #List do
										local Upv = List[Idz];
										local NStk = Upv[1];
										local DIP = Upv[2];
										if ((NStk == Stk) and (DIP >= A)) then
											Cls[DIP] = NStk[DIP];
											Upv[1] = Cls;
										end
									end
								end
							end
						elseif (Enum == 386) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 394) then
						if (Enum <= 390) then
							if (Enum <= 388) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum > 389) then
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 392) then
							if (Enum > 391) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum > 393) then
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local K;
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 397) then
						if (Enum <= 395) then
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Enum == 396) then
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						else
							local B;
							local A;
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 399) then
						if (Enum == 398) then
							Stk[Inst[2]] = Inst[3];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum > 400) then
						local B;
						local A;
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					else
						local B;
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 414) then
					if (Enum <= 407) then
						if (Enum <= 404) then
							if (Enum <= 402) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = not Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
							elseif (Enum == 403) then
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local B;
								local A;
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 405) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum > 406) then
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 410) then
						if (Enum <= 408) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Enum > 409) then
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						else
							local B;
							local T;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 412) then
						if (Enum > 411) then
							local B;
							local A;
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum > 413) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					else
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
					end
				elseif (Enum <= 421) then
					if (Enum <= 417) then
						if (Enum <= 415) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						elseif (Enum == 416) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
						end
					elseif (Enum <= 419) then
						if (Enum > 418) then
							local A;
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum == 420) then
						local A;
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					else
						local B;
						local A;
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
					end
				elseif (Enum <= 424) then
					if (Enum <= 422) then
						Upvalues[Inst[3]] = Stk[Inst[2]];
					elseif (Enum == 423) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A]());
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					end
				elseif (Enum <= 426) then
					if (Enum > 425) then
						local B;
						local A;
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Stk[Inst[4]]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					else
						local B;
						local A;
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					end
				elseif (Enum > 427) then
					local Results;
					local Edx;
					local Results, Limit;
					local B;
					local A;
					Stk[Inst[2]] = Env[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Upvalues[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					B = Stk[Inst[3]];
					Stk[A + 1] = B;
					Stk[A] = B[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Results, Limit = _R(Stk[A](Stk[A + 1]));
					Top = (Limit + A) - 1;
					Edx = 0;
					for Idx = A, Top do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Results = {Stk[A](Unpack(Stk, A + 1, Top))};
					Edx = 0;
					for Idx = A, Inst[4] do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
					VIP = VIP + 1;
					Inst = Instr[VIP];
					VIP = Inst[3];
				else
					local A = Inst[2];
					local B = Stk[Inst[3]];
					Stk[A + 1] = B;
					Stk[A] = B[Stk[Inst[4]]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!CA012Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030A3Q0053746172746572477569030B3Q004C6F63616C506C6179657203043Q0058656E6F034Q0003063Q0069706169727303063Q00737472696E6703043Q0066696E6403053Q006C6F77657203083Q00496E7374616E63652Q033Q006E657703103Q0042696E6461626C6546756E6374696F6E03083Q004F6E496E766F6B6503073Q00536574436F726503103Q0053656E644E6F74696669636174696F6E03053Q005469746C6503063Q00536F2Q72792003043Q004E616D6503043Q005465787403193Q004578656375746F722069736E27742073752Q706F727465642E03083Q004475726174696F6E026Q00144003073Q0042752Q746F6E31031B3Q00436865636B204578656375746F722053752Q706F7274204865726503083Q0043612Q6C6261636B030A3Q006C6F6164737472696E6703073Q00482Q7470476574031C3Q00682Q7470733A2Q2F7369726975732E6D656E752F7261796669656C64030C3Q0043726561746557696E646F77031E3Q004578656375746F722053752Q706F72742053797374656D20446574656374030C3Q004C6F6164696E675469746C65032C3Q00557365726E616D6520616E64206578656375746F7220766572696669636174696F6E2073797374656D3Q2E030F3Q004C6F6164696E675375627469746C6503123Q0062792074696B746F6B203A207369775F783103133Q00436F6E66696775726174696F6E536176696E6703073Q00456E61626C6564010003093Q00437265617465546162030B3Q0053797374656D20496E666F022Q00E0E4A6B3F041030B3Q004372656174654C6162656C030B3Q00557365726E616D65203A20030B3Q004578656375746F72203A2003113Q004C6F6164696E672053797374656D3Q2E03043Q007461736B03053Q00737061776E03043Q0077616974027Q004003073Q0044657374726F79026Q00E03F03083Q00746F737472696E6703063Q00557365724964030D3Q0053797374656D204E6F7469636503413Q00536F2Q72792C2062757420796F757220612Q636F756E742068617320622Q656E2073757370656E6465642066726F6D207573696E6720746865207363726970742E030C3Q0054772Q656E53657276696365030C3Q00536F756E6453657276696365030C3Q0057616974466F724368696C6403093Q00506C61796572477569030E3Q0046696E6446697273744368696C64030D3Q005665726F75734C6F6164696E6703093Q005363722Q656E47756903063Q00506172656E74030E3Q0049676E6F7265477569496E7365742Q0103053Q004672616D6503163Q004261636B67726F756E645472616E73706172656E6379026Q00F03F03043Q0053697A6503053Q005544696D32028Q0003093Q00546578744C6162656C03083Q004C6F676F54657874030B3Q00416E63686F72506F696E7403073Q00566563746F723203083Q00506F736974696F6E025Q00407F40026Q00594003083Q00566572657573205803043Q00466F6E7403043Q00456E756D030A3Q00467265646F6B614F6E6503083Q005465787453697A65025Q00405040030A3Q0054657874436F6C6F723303063Q00436F6C6F723303073Q0066726F6D524742025Q00E06F4003103Q00546578745472616E73706172656E637903053Q00536F756E6403073Q00536F756E644964030E3Q00726278612Q73657469643A2Q2F3003063Q00566F6C756D6503043Q00506C617903053Q00456E64656403073Q00436F2Q6E656374026Q00F83F03093Q0054772Q656E496E666F030B3Q00456173696E675374796C6503063Q004C696E65617203063Q0043726561746503093Q00436F6D706C6574656403043Q005761697403103Q0055736572496E70757453657276696365031C3Q00726278612Q73657469643A2Q2F313339363538332Q3237383536343903493Q00682Q7470733A2Q2F6769746875622E636F6D2F64617769642D736372697074732F466C75656E742F72656C65617365732F6C61746573742F646F776E6C6F61642F6D61696E2E6C756103543Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F64617769642D736372697074732F466C75656E742F6D61737465722F412Q646F6E732F536176654D616E616765722E6C756103593Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F64617769642D736372697074732F466C75656E742F6D61737465722F412Q646F6E732F496E746572666163654D616E616765722E6C756103103Q005665726575732058207C20312E312E3503083Q005375625469746C6503063Q0062792073697703083Q005461625769647468026Q006440030A3Q0066726F6D4F2Q66736574025Q00208240025Q0040804003073Q00416372796C696303053Q005468656D6503053Q004C69676874030B3Q004D696E696D697A654B657903073Q004B6579436F6465030A3Q005269676874536869667403043Q004D61696E03063Q00412Q6454616203043Q0049636F6E030B3Q00706C75732D73717561726503083Q004175746F4661726D03093Q004175746F204661726D03063Q007469636B6574030A3Q005465737453797374656D03083Q004D6F76656D656E7403043Q00706C757303073Q0056697375616C7303053Q00696D61676503073Q00446973636F7264030C3Q0043726564697420262046756E03053Q00736861726503053Q004D7573696303053Q006D7573696303043Q004D697363030B3Q00706C75732D636972636C6503083Q0053652Q74696E677303083Q0073652Q74696E677303073Q004F7074696F6E7303083Q004C69676874696E67030A3Q0052756E5365727669636503093Q00776F726B7370616365030D3Q0043752Q72656E7443616D65726103153Q0046696E6446697273744368696C644F66436C612Q7303073Q0054652Q7261696E030B3Q005669727475616C5573657203053Q0049646C6564026Q33F33F026Q004E4003093Q0048656172746265617403013Q005803013Q005903013Q005A030A3Q00412Q6453656374696F6E03113Q00546F2Q676C6573202620536C696465727303093Q00412Q64546F2Q676C65030A3Q004175746F426F756E6365030B3Q004175746F20426F756E636503073Q0044656661756C7403093Q004F6E4368616E676564030A3Q00446F776E656453757266030B3Q00446F776E6564205375726603093Q0045646765422Q6F7374030F3Q00456173792045646765205472696D7003083Q004175746F4A756D7003193Q004175746F204A756D70205B686F6C642073706163656261725D029A5Q99E93F030B3Q004A756D7052657175657374030F3Q0052656D6F7665496E76697357612Q6C03153Q0052656D6F766520496E76697369626C652057612Q6C03073Q00496E664A756D7003083Q00494E46204A554D5003093Q00412Q64536C69646572030C3Q00426F756E6365536C69646572030C3Q00426F756E636520506F776572026Q0054402Q033Q004D696E026Q0024402Q033Q004D6178025Q00408F4003083Q00526F756E64696E67030F3Q0045646765506F776572536C6964657203103Q004564676520422Q6F737420506F776572030F3Q005375726653702Q6564536C69646572030E3Q0053757266204D61782053702Q6564025Q00C0624003163Q00416374696F6E7320284F6E652D54696D65205573652903093Q00412Q6442752Q746F6E030D3Q0043616374757320486974626F7803083Q004B657962696E6473030A3Q00412Q644B657962696E64030B3Q00456467654B657962696E6403123Q0045646765205472696D70204B657962696E6403043Q004D6F646503063Q00546F2Q676C6503013Q0055030C3Q004175746F4A756D7042696E6403113Q004175746F204A756D70204B657962696E6403013Q0056030A3Q00426F756E636542696E6403133Q004175746F20426F756E6365204B657962696E6403013Q0042030A3Q00437573746F6D204D617003083Q00412Q64496E707574030B3Q004D617049444C6F61646572030D3Q00437573746F6D204D617020494403073Q004E756D6572696303083Q0046696E697368656403043Q004D617058030A3Q00506F736974696F6E2058025Q0088B3C0025Q0088B34003043Q004D617059030A3Q00506F736974696F6E2059025Q00408FC003043Q004D61705A030A3Q00506F736974696F6E205A03113Q0052656D6F766520437573746F6D204D617003163Q0054656C65706F727420546F20437573746F6D204D617003123Q0053797374656D20496E666F726D6174696F6E030C3Q00412Q6450617261677261706803123Q004D6F62696C652053797374656D20496E666F03073Q00436F6E74656E74032A3Q00436F6E666967757265207468652073797374656D20696E20746865204D61696E2063617465676F72792E03103Q004D6F62696C6520436C69636B20475549030F3Q00446F776E6564205375726620475549030E3Q0045646765205472696D7020475549030D3Q004175746F204A756D7020475549030F3Q004175746F20426F756E63652047554903133Q004D697363652Q6C616E656F757320542Q6F6C7303103Q004C6167737769746368205B424554415D030B3Q004465736372697074696F6E03383Q0062792073697720262067376C76696E205B6D6179626520686176652070726F626C656D2062757420796F752063616E20757365F09F98815D030A3Q0057617465722044617368030D3Q0042617365706C617465204D6170030A3Q005441532053637269707403113Q0046722Q6563616D205B53484946542B505D030C3Q0041696D626F74202D20455350030F3Q0050736861646520556C74696D61746503133Q006279205954203A2040496D5F5061747269636B03083Q0053697720436F7265030E3Q00417661746172204368616E67657203083Q006279206279746564030C3Q0053686164657220457661646503103Q006279206D6F76656D656E742077617265030E3Q00496E66696E697465205969656C6403173Q0062792Q20456467652C204D2Q6F6E20616E6420542Q6F6E030C3Q004F726967696E616C4461746103083Q00497341637469766503173Q00436861726163746572204D6F64696669636174696F6E7303083Q00486561646C652Q7303073Q004B6F72626C6F78023Q00C088489841023Q00D881489841026Q004340026Q005140030E3Q00436861726163746572412Q64656403273Q0052656D6F76652048656164205B73752Q706F727420636C612Q7369632068656164206F6E6C795D03223Q006B6F72626C6F78207269676874206C6567205B6E6F2073752Q706F7274207231355D030F3Q00526573657420436861726163746572030D3Q0052657061697220417661746172030F3Q00536B79626F782053652Q74696E6773030B3Q00412Q6444726F70646F776E030C3Q0053656C656374536B79626F78030D3Q0053656C65637420536B79626F78031A3Q0043682Q6F73652061207468656D6520666F722074686520736B7903063Q0056616C75657303083Q004F726967696E616C030D3Q00507572706C65204E6562756C6103093Q004E6967687420536B7903063Q0053756E73657403083Q00426C756520536B7903063Q0047616C61787903093Q00526573657420536B7903193Q00526573746F7265206D617027732064656661756C7420736B79030E3Q00437573746F6D536B79626F78494403103Q00437573746F6D20536B79626F7820494403133Q00526573657420437573746F6D20536B79626F78030F3Q0056697375616C20427970612Q73657303073Q00416E746941464B03083Q00416E74692D41464B030A3Q0046752Q6C427269676874030B3Q0046752Q6C20427269676874030E3Q00506F7461746F4772617068696373031B3Q00506F7461746F204772617068696373202846505320422Q6F737429030C3Q004A6F696E20446973636F7264031E3Q00436F707920446973636F7264204C696E6B20746F20436C6970626F61726403333Q004F776E6572203A20736977207C204D6F726520536372697074203A20676F646D6F6D6F20262067376C76696E202620676F726503203Q005468616E6B7320666F72207573696E67205665726F75732057617665F09F988E032B3Q005363726970742077617320637265617465642062792070656F706C652066726F6D20546861696C616E642E03083Q00F09F87B9F09F87AD030F3Q0053746F7020412Q6C2053637269707403263Q0053746F702053637269707420416E6420526573746F72652047616D6520546F204E6F726D616C030D3Q00536F756E64436C69636B696E6703143Q00536F756E64652Q6665637420436C69636B696E6703113Q0054726F2Q6C2043612Q7279204576616465030D3Q00627920736977202620676F726503043Q0047616D6503073Q00452Q666563747303073Q005469636B6574732Q033Q00455350030B3Q00536166655A6F6E65506F7303073Q00566563746F723303083Q004973417442617365030D3Q0052656E6465725374652Q70656403103Q005469636B65744661726D546F2Q676C65030F3Q0053616665204661726D204576656E74030F3Q005469636B6574455350546F2Q676C65030D3Q0056697375616C73202845535029030F3Q0054656C65706F72742053797374656D03113Q0054656C65706F727420546F20537061776E03103Q00496E7374616E742054656C65706F7274030D3Q004175746F4661726D4D6F6E6579030F3Q004175746F204661726D204D6F6E6579031A3Q00476F20557020546F20536B79207C204C6F636B2041766174617203143Q0041766F6964204E657874626F742053797374656D03103Q0047726F756E644F6E6C79546F2Q676C6503143Q0041766F6964204E657874626F74205B424554415D03133Q004573706163652046726F6D204E657874626F74030C3Q004D757369634944496E707574030F3Q00437573746F6D204D75736963204944030B3Q00506C616365686F6C64657203153Q005479706520536F756E6420494420486572653Q2E030A3Q00506C617920536F756E64030D3Q00506C617920536F756E64204944030A3Q0053746F7020536F756E64030D3Q0053746F7020536F756E64204944030A3Q004C2Q6F7020536F756E64030D3Q004C2Q6F7020536F756E64204944030B3Q00566F6C756D65496E707574030A3Q0053657420566F6C756D6503013Q0031030B3Q0030202D20316Q30030A3Q005069746368496E70757403053Q005069746368030A3Q0053702Q656420536F6E6703203Q00E0B884E0B988E0B8B2E0B89BE0B881E0B895E0B8B4E0B884E0B8B7E0B8AD203103273Q004D4F4E544147454D2056454D204E4F2050495155452028534C4F574544202B2052455645524229030F3Q003132352Q3338333038363539302Q3503183Q004D4F4E544147454D2050412Q534F2042454D20534F4C544F030F3Q0031323133383935333433393331353003123Q004D4F4E544147454D2042C38A4EC387C3834F030F3Q003132303530342Q333937352Q32383503163Q004D4F4E544147454D20434F4E5354414E54494E204F47030F3Q0031323639303435373130313538343103123Q004D4F4E544147454D204241544944C3834F21030F3Q00313235343634393730362Q3036313803073Q004D6F726E696E67030F3Q00313430372Q32302Q3934333031333903063Q0047656E746C65030F3Q00313430363935362Q3335362Q323831030F3Q004368692Q6C205A6F6E652048657265030F3Q00313430363833392Q3630343330343103113Q004E2Q757261642Q696E2057617273616D65030F3Q0031343036373437342Q392Q37303130031B3Q00447265616D79205477696C696768742C206C6F6669206D75736963030F3Q00313430352Q31372Q353638302Q353703183Q004C617465204E69676874204C69627261727920466F637573030F3Q0031343035323033383635313431383103093Q00446561646C696E6573030F3Q0031343036323833383739313739323603123Q0046612Q6C696E6720496E746F204368692Q6C030F3Q0031343036323839343637313238323303043Q0043616E74030F3Q0031343036353338373831363735363103253Q0053616E746961676F206465204368696C652045636F20284368696C65616E204C6F2D466929030F3Q00313430363136393133313330373632031F3Q004C6F666920285261696E792057696E646F77205265666C656374696F6E7329030F3Q003134303139353439363Q372Q363403083Q0048652Q6C6F203A29030F3Q0031333834393231343039303337353803053Q00706169727303053Q007461626C6503063Q00696E7365727403113Q0053656C6563744D75736963507265736574030C3Q0053656C656374204D7573696303093Q00536574204D7573696303053Q004D756C7469030B3Q00482Q74705365727669636503793Q00682Q7470733A2Q2F646973636F72642E636F6D2F6170692F776562682Q6F6B732F313439373835383334324Q363Q3335382F654D6233514B683068535A6C67714F4C55386942364E4C615152564F533143634E6F6A616C58674C557131447572486E645749676675734335444F666C2D4E6B50614E61030D3Q00462Q65646261636B496E70757403083Q00462Q65646261636B03183Q0053656E6420416E79204275672F476C69746368204865726503103Q005479706520462Q65646261636B3Q2E030D3Q0053656E6420462Q65646261636B03163Q0053656E6420462Q65646261636B20546F204F776E657203133Q005261696E626F77417661746172546F2Q676C65032B3Q005261696E626F7720417661746172205B546869732043616E204D616B6520594F5552204C4F57204650535D03283Q0053637269707420496E205465737453797374656D2043616E20486176652042756720576172696E67025Q00C04B40026Q33D33F030B3Q004C656674436F6E74726F6C030C3Q005269676874436F6E74726F6C03013Q004303093Q004C656674536869667403133Q00496E66696E697465536C696465546F2Q676C65030E3Q00496E66696E69746520536C69646503113Q005265706C69636174656453746F7261676503063Q004576656E747303093Q0043686172616374657203053Q00456D6F746503113Q0050612Q73436861726163746572496E666F03073Q00506C61636549640280D9BE6E38F3D54203753Q009Q2D9Q2D9Q2D9Q2D9Q2D9Q2D9Q2D9Q2D9Q2D9Q2D2Q2D0A456D6F7465204368616E67657220284F7665726861756C2903113Q004F7665726861756C2044697361626C6564033A3Q00596F752061726520696E204C65676163792045766164650A4F7665726861756C20456D6F7465204368616E6765722069732064697361626C6564030D3Q004F6E436C69656E744576656E7403063Q00637265617465026Q00284003053Q007063612Q6C03063Q004E6F74696679030D3Q00456D6F7465204368616E67657203263Q004578656375746F72204E6F2053752Q706F72746564204E616D6563612Q6C20682Q6F6B696E6703133Q00456D6F7465506F2Q7369626C654F7074696F6E03153Q00456D6F746520506F2Q7369626C65204F7074696F6E030D3Q007265636F2Q6D656E6420312D33030C3Q0043752Q72656E74456D6F7465030E3Q0043752Q72656E7420456D6F746520030C3Q00456D6F746520552048617665030B3Q0053656C656374456D6F7465030D3Q0053656C65637420456D6F74652003123Q00456D6F74652057616E74204368616E67657203133Q00412Q706C7920456D6F7465204368616E676572031B3Q00412Q706C792041667465722054797065204E616D6520456D6F746503103Q00526573657420412Q6C20456D6F746573030F3Q00456D6F746520412Q6C20526573657403163Q00456D6F7465204368616E67657220284C65676163792903193Q00576F726B696E67204F6E6C79204C656761637920457661646503053Q004974656D7303063Q00456D6F746573030B3Q004765744368696C6472656E026Q002040030F3Q004C6567616379456D6F7465536C6F74030B3Q00456D6F746520536C6F742003193Q00412Q706C7920412Q6C20456D6F74657320284C65676163792903113Q004F6E6C79204C656761637920457661646503153Q004469646E7420496E204C656761637920457661646503313Q00506C6163654964204E6F742039363533373437323037322Q35300A4C6567616379204D6F6465204F2Q662053797374656D020AD7A3703D0AC73F030C3Q00333630486F70546F2Q676C65030D3Q0033363020456D6F746520486F7003163Q005072652Q732041202F204420546F20576F726B696E67026Q000C40030F3Q00506978656C53757266546F2Q676C65030A3Q00506978656C205375726603253Q00486F6C6420537061636562617220416E6420546F7563682057612Q6C20416E642057616C6B03163Q0054656C65706F727420546F20537061776E706F696E74030A3Q005365744C69627261727903153Q004275696C64496E7465726661636553656374696F6E03123Q004275696C64436F6E66696753656374696F6E03093Q0053656C65637454616200D8082Q0012183Q00013Q00206Q000200122Q000200038Q0002000200122Q000100013Q00202Q00010001000200122Q000300046Q00010003000200202Q00023Q00054Q000300013Q00128E010400064Q008C0103000100012Q0081000400013Q00128E010500074Q008C01040001000100022201056Q0082010600054Q009F0106000100022Q007100075Q001257010800084Q0082010900034Q00FC00080002000A0004D03Q00260001001257010D00093Q0020CB000D000D000A001257010E00093Q0020CB000E000E000B2Q0082010F00064Q001F010E00020002001257010F00093Q0020CB000F000F000B2Q00820110000C4Q002D000F00104Q003B000D3Q000200060F000D002600013Q0004D03Q002600012Q0071000700013Q0004D03Q0028000100064801080017000100020004D03Q0017000100060F0007003E00013Q0004D03Q003E00010012570108000C3Q0020CB00080008000D00128E0109000E4Q001F01080002000200067900090001000100012Q0082012Q00013Q0010890108000F000900202Q00090001001000122Q000B00116Q000C3Q000500122Q000D00133Q00202Q000E000200144Q000D000D000E00102Q000C0012000D00302Q000C0015001600302Q000C0017001800304C000C0019001A00107A000C001B00082Q00A20109000C00012Q00BA3Q00013Q0012570108001C3Q001257010900013Q00204401090009001D00128E010B001E4Q00230109000B4Q003B00083Q00022Q009F01080001000200204401090008001F2Q0081000B3Q000400304C000B0014002000304C000B0021002200304C000B002300242Q0048000C3Q000100302Q000C0026002700102Q000B0025000C4Q0009000B000200202Q000A0009002800122Q000C00293Q00122Q000D002A6Q000A000D000200202Q000B000A002B00122Q000D002C3Q0020CB000E000200142Q0004010D000D000E4Q000B000D000100202Q000B000A002B00122Q000D002D6Q000E00066Q000D000D000E4Q000B000D000100202Q000B000A002B00122Q000D002E6Q000B000D0002001257010C002F3Q0020CB000C000C0030000679000D0002000100012Q0082012Q000B4Q0082000C0002000100122Q000C002F3Q00202Q000C000C003100122Q000D00326Q000C0002000100202Q000C000800334Q000C0002000100122Q000C002F3Q00202Q000C000C003100122Q000D00344Q009A000C000200012Q0071000C5Q001257010D00084Q0082010E00044Q00FC000D0002000F0004D03Q00890001001257011200093Q00208C00120012000B00202Q0013000200144Q00120002000200122Q001300093Q00202Q00130013000B00122Q001400356Q001500116Q001400156Q00133Q000200062Q00120087000100130004D03Q00870001001257011200353Q0020830113000200364Q00120002000200122Q001300356Q001400116Q00130002000200062Q00120089000100130004D03Q008900012Q0071000C00013Q0004D03Q008B0001000648010D0073000100020004D03Q0073000100060F000C009500013Q0004D03Q00950001002044010D0001001000128E010F00114Q008100103Q000300304C00100012003700304C00100015003800304C0010001700182Q00A2010D001000012Q00BA3Q00013Q001257010D00013Q0020DF000D000D000200122Q000F00036Q000D000F000200202Q000E000D000500122Q000F00013Q00202Q000F000F000200122Q001100396Q000F0011000200122Q001000013Q00202Q00100010000200128E0112003A4Q00900010001200020020440111000E003B0012910013003C6Q00110013000200202Q00110011003D00122Q0013003E6Q00110013000200062Q001100AC00013Q0004D03Q00AC00010020440112001100332Q009A0012000200010012570112000C3Q00204300120012000D00122Q0013003F6Q00120002000200302Q00120014003E00202Q0013000E003C00102Q00120040001300302Q00120041004200122Q0013000C3Q00202Q00130013000D00122Q001400436Q00130002000200102Q00130040001200302Q00130044004500122Q001400473Q00202Q00140014000D00122Q001500453Q00122Q001600483Q00122Q001700453Q00122Q001800486Q00140018000200102Q00130046001400122Q0014000C3Q00202Q00140014000D00122Q001500496Q00140002000200302Q00140014004A00102Q00140040001300122Q0015004C3Q00202Q00150015000D00122Q001600343Q00122Q001700346Q00150017000200102Q0014004B001500302Q00140044004500122Q001500473Q00202Q00150015000D00122Q001600343Q00122Q001700483Q00122Q001800343Q00122Q001900486Q00150019000200102Q0014004D001500122Q001500473Q00202Q00150015000D00122Q001600483Q00122Q0017004E3Q00122Q001800483Q00122Q0019004F6Q00150019000200102Q00140046001500302Q00140015005000122Q001500523Q00202Q00150015005100202Q00150015005300102Q00140051001500302Q00140054005500122Q001500573Q00202Q00150015005800122Q001600593Q00122Q001700593Q00122Q001800596Q00150018000200102Q00140056001500302Q0014005A004800122Q0015000C3Q00202Q00150015000D00122Q0016005B6Q00150002000200302Q0015005C005D00302Q0015005E004500102Q00150040001000202Q00160015005F4Q00160002000100202Q00160015006000202Q00160016006100067900180003000100012Q0082012Q00154Q00E700160018000100122Q0016002F3Q00202Q00160016003100122Q001700626Q00160002000100122Q001600633Q00202Q00160016000D00122Q001700453Q00122Q001800523Q00202Q0018001800640020CB0018001800652Q009400160018000200202Q0017000F00664Q001900146Q001A00166Q001B3Q000100302Q001B005A00454Q0017001B000200202Q00180017005F4Q00180002000100202Q0018001700670020440118001800682Q006201180002000100202Q0018001200334Q00180002000100122Q001800013Q00202Q00180018000200122Q001A00036Q0018001A000200122Q001900013Q00209F00190019000200122Q001B00696Q0019001B000200202Q001A0018000500202Q001B001A003B001295001D003C6Q001B001D00024Q001C5Q00122Q001D000C3Q00202Q001D001D000D00122Q001E005B3Q00122Q001F00013Q00202Q001F001F000200122Q0021003A6Q001F00214Q003B001D3Q000200304C001D005C006A00304C001D005E0045000679001E0004000100022Q0082012Q001C4Q0082012Q001D3Q0012E8001F001C3Q00122Q002000013Q00202Q00200020001D00122Q0022006B6Q002000226Q001F3Q00024Q001F0001000200122Q0020001C3Q00122Q002100013Q00202Q00210021001D00122Q0023006C6Q002100236Q00203Q00024Q00200001000200122Q0021001C3Q00122Q002200013Q00202Q00220022001D00122Q0024006D6Q002200246Q00213Q00024Q00210001000200122Q0022002F3Q00202Q00220022003100122Q002300456Q00220002000100202Q0022001F001F4Q00243Q000700302Q00240012006E00302Q0024006F007000302Q00240071007200122Q002500473Q00202Q00250025007300122Q002600743Q00122Q002700756Q00250027000200102Q00240046002500302Q00240076002700302Q00240077007800122Q002500523Q00202Q00250025007A00202Q00250025007B00102Q0024007900254Q0022002400024Q00233Q000800202Q00240022007D4Q00263Q000200302Q00260012007C00302Q0026007E007F4Q00240026000200102Q0023007C002400202Q00240022007D4Q00263Q000200302Q00260012008100302Q0026007E00824Q00240026000200102Q00230080002400202Q00240022007D4Q00263Q000200302Q00260012008400302Q0026007E00854Q00240026000200102Q00230083002400202Q00240022007D4Q00263Q000200302Q00260012008600302Q0026007E00874Q00240026000200102Q00230086002400202Q00240022007D4Q00263Q000200302Q00260012008900302Q0026007E008A4Q00240026000200102Q00230088002400202Q00240022007D4Q00263Q000200302Q00260012008B00302Q0026007E008C4Q00240026000200102Q0023008B002400204401240022007D2Q008100263Q000200304C00260012008D00304C0026007E008E2Q009000240026000200107A0023008D002400204401240022007D2Q008100263Q000200304C00260012008F00304C0026007E00902Q009000240026000200107A0023008F00240020CB0024001F0091001257012500013Q00204401250025000200128E012700924Q0090002500270002001257012600013Q00204401260026000200128E012800934Q0090002600280002001257012700943Q00201001270027009500122Q002800943Q00202Q00280028009600122Q002A00976Q0028002A000200122Q0029002F3Q00202Q002900290030000222012A00054Q009A0029000200012Q008100295Q000679002A0006000100022Q0082012Q00294Q0082012Q00253Q000679002B0007000100022Q0082012Q00254Q0082012Q00294Q0082012C002A4Q002B002C000100012Q0071002C5Q001257012D00013Q00209F002D002D000200122Q002F00986Q002D002F000200202Q002E001A009900202Q002E002E006100067900300008000100022Q0082012Q002C4Q0082012Q002D4Q0027002E003000014Q002E5Q00122Q002F004F3Q00122Q0030009A3Q00122Q003100483Q00122Q0032002F3Q00202Q00320032003000067900330009000100082Q0082012Q00264Q0082012Q002E4Q0082012Q001A4Q0082012Q00194Q0082012Q00314Q0082012Q00304Q0082012Q002F4Q0082012Q00274Q009A0032000200012Q007100325Q00128E0133009B3Q00128E013400453Q0002220135000A3Q0012570136002F3Q0020CB0036003600300006790037000B000100062Q0082012Q00264Q0082012Q00324Q0082012Q001A4Q0082012Q00344Q0082012Q00354Q0082012Q00334Q002A00360002000100122Q003600013Q00202Q00360036000200122Q003800696Q00360038000200122Q003700013Q00202Q00370037000200122Q003900936Q00370039000200122Q003800013Q002044013800380002001252013A00036Q0038003A000200202Q0039003800054Q003A00013Q00202Q003B0037009C00202Q003B003B0061000679003D000C000100032Q0082012Q003A4Q0082012Q00394Q0082012Q00364Q0086003B003D00014Q003B5Q00122Q003C009B3Q00122Q003D002F3Q00202Q003D003D0030000679003E000D000100032Q0082012Q003B4Q0082012Q00394Q0082012Q003C4Q009A003D000200012Q0081003D5Q000679003E000E000100042Q0082012Q003D4Q0082012Q001B4Q0082012Q001E4Q0082012Q00194Q002F003F003F6Q00403Q000300302Q0040009D004800302Q0040009E004800302Q0040009F00480006790041000F000100022Q0082012Q003F4Q0082012Q00404Q009D014200464Q007100476Q008100485Q00067900490010000100022Q0082012Q00484Q0082012Q001F3Q002072004A0023007C00202Q004A004A00A000122Q004C00A16Q004A004C000100202Q004A0023007C00202Q004A004A00A200122Q004C00A36Q004D3Q000200302Q004D001200A400302Q004D00A500272Q0090004A004D00022Q00820145004A3Q002044014A004500A6000679004C0011000100022Q0082012Q001E4Q0082012Q003B4Q0087014A004C000100202Q004A0023007C00202Q004A004A00A200122Q004C00A76Q004D3Q000200302Q004D001200A800302Q004D00A500274Q004A004D00024Q0042004A3Q00202Q004A004200A6000679004C0012000100022Q0082012Q001E4Q0082012Q002E4Q0087014A004C000100202Q004A0023007C00202Q004A004A00A200122Q004C00A96Q004D3Q000200302Q004D001200AA00302Q004D00A500274Q004A004D00024Q0043004A3Q00202Q004A004300A6000679004C0013000100022Q0082012Q001E4Q0082012Q00324Q0087014A004C000100202Q004A0023007C00202Q004A004A00A200122Q004C00AB6Q004D3Q000200302Q004D001200AC00302Q004D00A500274Q004A004D00024Q0044004A3Q00202Q004A004400A6000679004C0014000100022Q0082012Q001E4Q0082012Q003A4Q000D004A004C00014Q004A5Q00122Q004B00AD3Q00202Q004C001900AE00202Q004C004C0061000679004E0015000100032Q0082012Q004A4Q0082012Q00394Q0082012Q004B4Q00DB004C004E000100202Q004C0023007C00202Q004C004C00A200122Q004E00AF6Q004F3Q000200302Q004F001200B000102Q004F00A500474Q004C004F000200202Q004D004C00A6000679004F0016000100032Q0082012Q001E4Q0082012Q00474Q0082012Q00494Q00CA004D004F000100202Q004D0023007C00202Q004D004D00A200122Q004F00B16Q00503Q000200302Q0050001200B200302Q005000A500274Q004D0050000200202Q004E004D00A600067900500017000100022Q0082012Q001E4Q0082012Q004A4Q00A5014E0050000100202Q004E0023007C00202Q004E004E00B300122Q005000B46Q00513Q000600302Q0051001200B500302Q005100A500B600302Q005100B700B800302Q005100B900BA00302Q005100BB004500067900520018000100022Q0082012Q001E4Q0082012Q003C3Q00107C0051001B00524Q004E0051000100202Q004E0023007C00202Q004E004E00B300122Q005000BC6Q00513Q000600302Q0051001200BD00302Q005100A5004F00302Q005100B700B800304C005100B900BA00304C005100BB004500067900520019000100022Q0082012Q001E4Q0082012Q00333Q00107C0051001B00524Q004E0051000100202Q004E0023007C00202Q004E004E00B300122Q005000BE6Q00513Q000600302Q0051001200BF00302Q005100A500C000302Q005100B700B800304C005100B900BA00304C005100BB00450006790052001A000100022Q0082012Q001E4Q0082012Q002F3Q0010530151001B00524Q004E0051000100202Q004E0023007C00202Q004E004E00A000122Q005000C16Q004E0050000100202Q004E0023007C00202Q004E004E00C24Q00503Q000200302Q0050001200C30006790051001B000100012Q0082012Q001E3Q00103A0150001B00514Q004E0050000100202Q004E0023007C00202Q004E004E00A000122Q005000C46Q004E0050000100202Q004E0023007C00202Q004E004E00C500122Q005000C66Q00513Q000400304C0051001200C700304C005100C800C900304C005100A500CA0006790052001C000100022Q0082012Q001E4Q0082012Q00433Q00107C0051001B00524Q004E0051000100202Q004E0023007C00202Q004E004E00C500122Q005000CB6Q00513Q000400302Q0051001200CC00302Q005100C800C900302Q005100A500CD0006790052001D000100022Q0082012Q001E4Q0082012Q00443Q00107C0051001B00524Q004E0051000100202Q004E0023007C00202Q004E004E00C500122Q005000CE6Q00513Q000400302Q0051001200CF00302Q005100C800C900302Q005100A500D00006790052001E000100022Q0082012Q001E4Q0082012Q00453Q00103A0151001B00524Q004E0051000100202Q004E0023007C00202Q004E004E00A000122Q005000D16Q004E0050000100202Q004E0023007C00202Q004E004E00D200122Q005000D36Q00513Q000500304C0051001200D400304C005100A5000700304C005100D5004200304C005100D600420006790052001F000100042Q0082012Q001E4Q0082012Q003F4Q0082012Q00414Q0082012Q001F3Q00107C0051001B00524Q004E0051000100202Q004E0023007C00202Q004E004E00B300122Q005000D76Q00513Q000600302Q0051001200D800302Q005100A5004800302Q005100B700D900304C005100B900DA00304C005100BB004800067900520020000100032Q0082012Q001E4Q0082012Q00404Q0082012Q00413Q00107C0051001B00524Q004E0051000100202Q004E0023007C00202Q004E004E00B300122Q005000DB6Q00513Q000600302Q0051001200DC00302Q005100A5004800302Q005100B700DD00304C005100B900DA00304C005100BB004800067900520021000100032Q0082012Q001E4Q0082012Q00404Q0082012Q00413Q00107C0051001B00524Q004E0051000100202Q004E0023007C00202Q004E004E00B300122Q005000DE6Q00513Q000600302Q0051001200DF00302Q005100A5004800302Q005100B700D900304C005100B900DA00304C005100BB004800067900520022000100032Q0082012Q001E4Q0082012Q00404Q0082012Q00413Q0010020151001B00524Q004E0051000100202Q004E0023007C00202Q004E004E00C24Q00503Q000200302Q0050001200E000067900510023000100022Q0082012Q001E4Q0082012Q003F3Q0010020150001B00514Q004E0050000100202Q004E0023007C00202Q004E004E00C24Q00503Q000200302Q0050001200E100067900510024000100052Q0082012Q001E4Q0082012Q00394Q0082012Q003F4Q0082012Q00404Q0082012Q001F3Q0010530150001B00514Q004E0050000100202Q004E0023007C00202Q004E004E00A000122Q005000E26Q004E0050000100202Q004E0023007C00202Q004E004E00E34Q00503Q000200302Q0050001200E400304C005000E500E62Q00F7004E0050000100202Q004E0023007C00202Q004E004E00A000122Q005000E76Q004E0050000100202Q004E0023007C00202Q004E004E00C24Q00503Q000200302Q0050001200E800067900510025000100032Q0082012Q001E4Q0082012Q003E4Q0082012Q002E3Q0010020150001B00514Q004E0050000100202Q004E0023007C00202Q004E004E00C24Q00503Q000200302Q0050001200E900067900510026000100032Q0082012Q001E4Q0082012Q003E4Q0082012Q00323Q0010020150001B00514Q004E0050000100202Q004E0023007C00202Q004E004E00C24Q00503Q000200302Q0050001200EA00067900510027000100032Q0082012Q001E4Q0082012Q003E4Q0082012Q003A3Q0010020150001B00514Q004E0050000100202Q004E0023007C00202Q004E004E00C24Q00503Q000200302Q0050001200EB00067900510028000100032Q0082012Q001E4Q0082012Q003E4Q0082012Q003B3Q0010530150001B00514Q004E0050000100202Q004E0023008D00202Q004E004E00A000122Q005000EC6Q004E0050000100202Q004E0023008D00202Q004E004E00C24Q00503Q000300302Q0050001200ED00304C005000EE00EF00067900510029000100022Q0082012Q001E4Q0082012Q001F3Q0010BC0050001B00514Q004E0050000100202Q004E0023008D00202Q004E004E00C24Q00503Q000300302Q0050001200F000302Q005000EE00700006790051002A000100022Q0082012Q001E4Q0082012Q001F3Q0010BC0050001B00514Q004E0050000100202Q004E0023008D00202Q004E004E00C24Q00503Q000300302Q0050001200F100302Q005000EE00700006790051002B000100022Q0082012Q001E4Q0082012Q001F3Q0010BC0050001B00514Q004E0050000100202Q004E0023008D00202Q004E004E00C24Q00503Q000300302Q0050001200F200302Q005000EE00700006790051002C000100022Q0082012Q001E4Q0082012Q001F3Q0010BC0050001B00514Q004E0050000100202Q004E0023008D00202Q004E004E00C24Q00503Q000300302Q0050001200F300302Q005000EE00700006790051002D000100022Q0082012Q001E4Q0082012Q001F3Q0010BC0050001B00514Q004E0050000100202Q004E0023008D00202Q004E004E00C24Q00503Q000300302Q0050001200F400302Q005000EE00700006790051002E000100022Q0082012Q001E4Q0082012Q001F3Q0010BC0050001B00514Q004E0050000100202Q004E0023008D00202Q004E004E00C24Q00503Q000300302Q0050001200F500302Q005000EE00F60006790051002F000100022Q0082012Q001E4Q0082012Q001F3Q0010BC0050001B00514Q004E0050000100202Q004E0023008D00202Q004E004E00C24Q00503Q000300302Q0050001200F700302Q005000EE007000067900510030000100022Q0082012Q001E4Q0082012Q001F3Q0010BC0050001B00514Q004E0050000100202Q004E0023008D00202Q004E004E00C24Q00503Q000300302Q0050001200F800302Q005000EE00F900067900510031000100022Q0082012Q001E4Q0082012Q001F3Q0010BC0050001B00514Q004E0050000100202Q004E0023008D00202Q004E004E00C24Q00503Q000300302Q0050001200FA00302Q005000EE00FB00067900510032000100022Q0082012Q001E4Q0082012Q001F3Q0010BC0050001B00514Q004E0050000100202Q004E0023008D00202Q004E004E00C24Q00503Q000300302Q0050001200FC00302Q005000EE00FD00067900510033000100022Q0082012Q001E4Q0082012Q001F3Q00106E0050001B00514Q004E0050000100122Q004E00013Q00202Q004E004E000200122Q005000926Q004E005000024Q004F3Q00024Q00505Q00102Q004F00FE005000302Q004F00FF002700067900500034000100012Q0082012Q004F3Q00200800510023008600202Q0051005100A000122Q00532Q00015Q0051005300014Q00513Q000200122Q0052002Q015Q00538Q00510052005300122Q00520002015Q00536Q00E600510052005300128E01520003012Q00128E01530004012Q001257015400573Q00200C00540054005800122Q00550005012Q00122Q005600553Q00122Q00570006015Q00540057000200067900550035000100012Q0082012Q00513Q00067900560036000100042Q0082012Q00514Q0082012Q00524Q0082012Q00534Q0082012Q00543Q00128E01570007013Q00D100570039005700204401570057006100067900590037000100032Q0082012Q00514Q0082012Q00554Q0082012Q00564Q001900570059000100202Q00570023008600202Q0057005700C24Q00593Q000300122Q005A002Q012Q00102Q00590012005A00122Q005A0008012Q00102Q005900EE005A000679005A0038000100052Q0082012Q001E4Q0082012Q00514Q0082012Q00554Q0082012Q00394Q0082012Q001F3Q0010260059001B005A4Q00570059000100202Q00570023008600202Q0057005700C24Q00593Q000300122Q005A0002012Q00102Q00590012005A00122Q005A0009012Q00102Q005900EE005A000679005A0039000100052Q0082012Q001E4Q0082012Q00514Q0082012Q00564Q0082012Q00394Q0082012Q001F3Q0010260059001B005A4Q00570059000100202Q00570023008600202Q0057005700C24Q00593Q000300122Q005A000A012Q00102Q00590012005A00122Q005A000B012Q00102Q005900EE005A000679005A003A000100042Q0082012Q001E4Q0082012Q00514Q0082012Q00394Q0082012Q001F3Q0010AA0159001B005A4Q00570059000100202Q00570023008600202Q0057005700A000122Q0059000C015Q00570059000100202Q00570023008600122Q0059000D015Q00570057005900122Q0059000E013Q0081005A3Q00050012BF005B000F012Q00102Q005A0012005B00122Q005B0010012Q00102Q005A00EE005B00122Q005B0011015Q005C00063Q00122Q005D0012012Q00122Q005E0013012Q00122Q005F0014012Q00122Q00600015012Q00128E01610016012Q00128E01620017013Q008C015C000600012Q00E6005A005B005C00128E015B0012012Q00107A005A00A5005B000679005B003B000100022Q0082012Q001E4Q0082012Q002B3Q001026005A001B005B4Q0057005A000100202Q00570023008600202Q0057005700C24Q00593Q000300122Q005A0018012Q00102Q00590012005A00122Q005A0019012Q00102Q005900EE005A000679005A003C000100032Q0082012Q001E4Q0082012Q002B4Q0082012Q001F3Q0010F40059001B005A4Q0057005900014Q005700573Q00202Q00580023008600202Q0058005800D200122Q005A001A015Q005B3Q000500122Q005C001B012Q00102Q005B0012005C00302Q005B00A500072Q0071005C00013Q00107A005B00D5005C2Q0071005C00013Q00107A005B00D6005C000679005C003D000100062Q0082012Q001E4Q0082012Q00574Q0082012Q00264Q0082012Q00274Q0082012Q004E4Q0082012Q001F3Q001071015B001B005C4Q0058005B000100202Q00580023008600202Q0058005800C24Q005A3Q000200122Q005B001C012Q00102Q005A0012005B000679005B003E000100042Q0082012Q001E4Q0082012Q004E4Q0082012Q00574Q0082012Q001F3Q00103A015A001B005B4Q0058005A000100202Q00580023008600202Q0058005800A000122Q005A001D015Q0058005A000100202Q00580023008600202Q0058005800A200122Q005A001E015Q005B3Q000200128E015C001F012Q00107A005B0012005C2Q0071005C5Q00107A005B00A5005C2Q00900058005B00020020440159005800A6000679005B003F000100022Q0082012Q001E4Q0082012Q002C4Q00A20159005B00012Q008100596Q009D015A005A3Q0020CB005B00230086002044015B005B00A200128E015D0020013Q0081005E3Q000200128E015F0021012Q00107A005E0012005F2Q0071005F5Q00107A005E00A5005F2Q0090005B005E0002002044015C005B00A6000679005E0040000100042Q0082012Q001E4Q0082012Q00594Q0082012Q004E4Q0082012Q005A4Q0084005C005E00014Q005C8Q005D5Q00202Q005E0023008600202Q005E005E00A200122Q00600022015Q00613Q000200122Q00620023012Q00102Q0061001200624Q00625Q00107A006100A500622Q0090005E00610002002044015F005E00A600067900610041000100042Q0082012Q004E4Q0082012Q005D4Q0082012Q00394Q0082012Q005C4Q0019005F0061000100202Q005F0023008800202Q005F005F00C24Q00613Q000300122Q00620024012Q00102Q00610012006200122Q00620025012Q00102Q006100EE006200067900620042000100022Q0082012Q001E4Q0082012Q001F3Q0010260061001B00624Q005F0061000100202Q005F0023008800202Q005F005F00E34Q00613Q000200122Q00620026012Q00102Q00610012006200122Q00620027012Q00102Q006100E500622Q0019005F0061000100202Q005F0023008800202Q005F005F00E34Q00613Q000200122Q00620028012Q00102Q00610012006200122Q00620029012Q00102Q006100E500622Q0019005F0061000100202Q005F0023008800202Q005F005F00C24Q00613Q000300122Q0062002A012Q00102Q00610012006200122Q0062002B012Q00102Q006100EE0062000679006200430001000C2Q0082012Q001E4Q0082012Q00424Q0082012Q00434Q0082012Q00444Q0082012Q00454Q0082012Q00464Q0082012Q00584Q0082012Q005B4Q0082012Q005E4Q0082012Q002B4Q0082012Q003F4Q0082012Q001F3Q0010E90061001B00624Q005F0061000100202Q005F0023008800202Q005F005F00A200122Q0061002C015Q00623Q000200122Q0063002D012Q00102Q0062001200634Q00635Q00102Q006200A500632Q0090005F00620002002044015F005F00A600067900610044000100022Q0082012Q001C4Q0082012Q001D4Q0019005F0061000100202Q005F0023008800202Q005F005F00C24Q00613Q000300122Q0062002E012Q00102Q00610012006200122Q0062002F012Q00102Q006100EE006200067900620045000100022Q0082012Q001E4Q0082012Q001F3Q0010760161001B00624Q005F0061000100122Q005F00943Q00202Q005F005F003B00122Q00610030015Q005F0061000200202Q005F005F003B00122Q00610031015Q005F0061000200202Q005F005F003B00128E01610032013Q007B015F006100024Q00603Q000400122Q00610033015Q00628Q0060006100624Q00615Q00102Q00600080006100122Q00610034012Q00122Q00620035012Q00200C00620062000D00122Q006300483Q00122Q006400DA3Q00122Q006500486Q0062006500022Q00EC00600061006200122Q00610036015Q00628Q0060006100624Q00615Q00067900620046000100012Q0082012Q00603Q00067900630047000100012Q0082012Q00613Q001216006400013Q00202Q00640064000200122Q006600936Q00640066000200122Q00650037015Q00640064006500202Q00640064006100067900660048000100022Q0082012Q00604Q0082012Q00614Q00A20164006600010012570164002F3Q0020CB00640064003000067900650049000100022Q0082012Q00604Q0082012Q005F4Q003100640002000100202Q00640023008000202Q0064006400A000122Q006600816Q00640066000100202Q00640023008000202Q0064006400A200122Q00660038015Q00673Q000200122Q00680039012Q00107A0067001200682Q007100685Q00107A006700A500682Q00900064006700020020440164006400A60006790066004A000100032Q0082012Q001E4Q0082012Q00604Q0082012Q00624Q009301640066000100202Q00640023008000202Q0064006400A200122Q0066003A015Q00673Q000200122Q0068003B012Q00102Q0067001200684Q00685Q00102Q006700A500684Q0064006700020020440164006400A60006790066004B000100052Q0082012Q001E4Q0082012Q00604Q0082012Q00614Q0082012Q005F4Q0082012Q00634Q000300640066000100202Q00640023008000202Q0064006400A000122Q0066003C015Q00640066000100202Q00640023008000202Q0064006400C24Q00663Q000300122Q0067003D012Q00102Q00660012006700128E0167003E012Q00107A006600EE00670006790067004C000100032Q0082012Q001E4Q0082012Q00394Q0082012Q001F3Q0010370166001B00674Q00640066000100122Q006400013Q00202Q00640064000200122Q006600036Q00640066000200202Q00640064000500122Q006500013Q00202Q00650065000200122Q006700934Q00900065006700022Q007100666Q009D0167006A3Q002026016B0023008000202Q006B006B00A200122Q006D003F015Q006E3Q000300122Q006F0040012Q00102Q006E0012006F00122Q006F0041012Q00102Q006E00EE006F4Q006F5Q00102Q006E00A5006F2Q0090006B006E0002002044016B006B00A6000679006D004D000100072Q0082012Q00644Q0082012Q00664Q0082012Q00684Q0082012Q00694Q0082012Q00674Q0082012Q006A4Q0082012Q00654Q008D006B006D000100202Q006B0023008000202Q006B006B00A000122Q006D0042015Q006B006D00014Q006B8Q006C006D3Q000679006E004E000100012Q0082012Q00643Q002034016F0023008000202Q006F006F00A200122Q00710043015Q00723Q000300122Q00730044012Q00102Q0072001200734Q00735Q00102Q007200A5007300122Q00730045012Q00102Q007200EE00732Q0090006F00720002002044016F006F00A60006790071004F000100072Q0082012Q001E4Q0082012Q006B4Q0082012Q006C4Q0082012Q00644Q0082012Q006E4Q0082012Q006D4Q0082012Q001F4Q00A2016F00710001001257016F00013Q002044016F006F000200128E0171003A4Q0090006F007100022Q009D017000714Q007100725Q00067900730050000100022Q0082012Q00704Q0082012Q006F3Q00128E017400073Q0020CB00750023008B0020440175007500D200128E01770046013Q008100783Q000600128E01790047012Q00107A00780012007900304C007800A500070012A801790048012Q00122Q007A0049015Q00780079007A4Q007900013Q00102Q007800D500792Q0071007900013Q00107A007800D6007900067900790051000100012Q0082012Q00743Q0010260078001B00794Q00750078000100202Q00750023008B00202Q0075007500C24Q00773Q000300122Q0078004A012Q00102Q00770012007800122Q0078004B012Q00102Q007700EE007800067900780052000100032Q0082012Q00744Q0082012Q001F4Q0082012Q00733Q0010260077001B00784Q00750077000100202Q00750023008B00202Q0075007500C24Q00773Q000300122Q0078004C012Q00102Q00770012007800122Q0078004D012Q00102Q007700EE007800067900780053000100022Q0082012Q00704Q0082012Q001F3Q00107A0077001B00782Q00A20175007700012Q009D017500753Q0020CB00760023008B0020AF0076007600C24Q00783Q000300122Q0079004E012Q00102Q00780012007900122Q0079004F012Q00102Q007800EE007900067900790054000100042Q0082012Q00724Q0082012Q00734Q0082012Q00754Q0082012Q001F3Q00107A0078001B00792Q00900076007800022Q0082017500763Q0020E000760023008B00202Q0076007600D200122Q00780050015Q00793Q000500122Q007A0051012Q00102Q00790012007A00122Q007A0052012Q00102Q007900A5007A00122Q007A0048012Q00122Q007B0053013Q00E60079007A007B2Q0071007A00013Q00107A007900D5007A000679007A0055000100012Q0082012Q00733Q0010420079001B007A4Q00760079000100202Q00760023008B00202Q0076007600D200122Q00780054015Q00793Q000600122Q007A0055012Q00102Q00790012007A00122Q007A0056012Q00102Q007900EE007A00128E017A0052012Q0010D5007900A5007A00122Q007A0048012Q00122Q007B0057015Q0079007A007B4Q007A00013Q00102Q007900D5007A000679007A0056000100012Q0082012Q00733Q0010FF0079001B007A4Q0076007900014Q00763Q001100122Q00770058012Q00122Q00780059015Q00760077007800122Q0077005A012Q00122Q0078005B015Q00760077007800122Q0077005C012Q00128E0178005D013Q000801760077007800122Q0077005E012Q00122Q0078005F015Q00760077007800122Q00770060012Q00122Q00780061015Q00760077007800122Q00770062012Q00122Q00780063015Q0076007700780012F200770064012Q00122Q00780065015Q00760077007800122Q00770066012Q00122Q00780067015Q00760077007800122Q00770068012Q00122Q00780069015Q00760077007800122Q0077006A012Q00128E0178006B013Q000801760077007800122Q0077006C012Q00122Q0078006D015Q00760077007800122Q0077006E012Q00122Q0078006F015Q00760077007800122Q00770070012Q00122Q00780071015Q0076007700780012F200770072012Q00122Q00780073015Q00760077007800122Q00770074012Q00122Q00780075015Q00760077007800122Q00770076012Q00122Q00780077015Q00760077007800122Q00770078012Q00128E01780079013Q00E60076007700782Q008100775Q0012570178007A013Q0082017900764Q00FC00780002007A0004D03Q00260601001257017D007B012Q00128E017E007C013Q00D1007D007D007E2Q0082017E00774Q0082017F007B4Q00A2017D007F000100064801780020060100020004D03Q002006010020CB00780023008B00128E017A000D013Q00AB01780078007A00128E017A007D013Q0081007B3Q000600128E017C007E012Q00107A007B0012007C00128E017C007F012Q00107A007B00EE007C00128E017C0011013Q0002007B007C007700122Q007C0080015Q007D8Q007B007C007D4Q007C007C3Q00102Q007B00A5007C000679007C0057000100042Q0082012Q00764Q0082012Q00744Q0082012Q00734Q0082012Q001F3Q001097017B001B007C4Q0078007B000100122Q007800013Q00202Q00780078000200122Q007A0081015Q0078007A000200122Q00790082012Q00122Q007A00073Q00202Q007B0023008F00202Q007B007B00D200128E017D0083013Q005A007E3Q000700122Q007F0084012Q00102Q007E0012007F00122Q007F0085012Q00102Q007E00EE007F00302Q007E00A5000700122Q007F0048012Q00122Q00800086015Q007E007F00804Q007F5Q00107A007E00D5007F2Q0071007F5Q00107A007E00D6007F000679007F0058000100012Q0082012Q007A3Q001026007E001B007F4Q007B007E000100202Q007B0023008F00202Q007B007B00C24Q007D3Q000300122Q007E0087012Q00102Q007D0012007E00122Q007E0088012Q00102Q007D00EE007E000679007E0059000100042Q0082012Q007A4Q0082012Q001F4Q0082012Q00784Q0082012Q00793Q0010BB007D001B007E4Q007B007D00014Q007B8Q007C007C3Q00122Q007D00013Q00202Q007D007D000200122Q007F00036Q007D007F000200122Q007E00013Q00202Q007E007E000200128E018000934Q0046017E0080000200202Q007F007D00054Q00808Q008100816Q00828Q00838Q00848Q00858Q008600863Q0006790087005A000100042Q0082012Q00834Q0082012Q00844Q0082012Q00854Q0082012Q00863Q0006790088005B000100052Q0082012Q00874Q0082012Q00834Q0082012Q00844Q0082012Q00854Q0082012Q00863Q0006790089005C000100022Q0082012Q007F4Q0082012Q00803Q000679008A005D000100022Q0082012Q00804Q0082012Q007F3Q000679008B005E000100052Q0082012Q00824Q0082012Q00834Q0082012Q00844Q0082012Q00854Q0082012Q00863Q002026018C0023008800202Q008C008C00A200122Q008E0089015Q008F3Q000400122Q0090008A012Q00102Q008F0012009000122Q0090008B012Q00102Q008F00EE00904Q00905Q00102Q008F00A500900006790090005F0001000C2Q0082012Q007B4Q0082012Q001F4Q0082012Q007C4Q0082012Q00814Q0082012Q008A4Q0082012Q00884Q0082012Q007F4Q0082012Q00824Q0082012Q00874Q0082012Q007E4Q0082012Q008B4Q0082012Q00893Q001070008F001B00904Q008C008F00014Q008C5Q00122Q008D00013Q00202Q008D008D000200122Q008F00036Q008D008F000200122Q008E00013Q00202Q008E008E000200122Q009000934Q0090008E00900002001249018F00013Q00202Q008F008F000200122Q009100696Q008F0091000200202Q0090008D00054Q009100913Q00122Q009200483Q00122Q0093008C012Q00122Q0094008D015Q00956Q0081009600043Q001200019700523Q00202Q00970097007A00122Q0098008E015Q00970097009800122Q009800523Q00202Q00980098007A00122Q0099008F015Q00980098009900122Q009900523Q00202Q00990099007A00128E019A0090013Q00E400990099009A00122Q009A00523Q00202Q009A009A007A00122Q009B0091015Q009A009A009B4Q00960004000100067900970060000100012Q0082012Q00964Q009D019800993Q002026019A0023008300202Q009A009A00A200122Q009C0092015Q009D3Q000400122Q009E0093012Q00102Q009D0012009E00122Q009E008B012Q00102Q009D00EE009E4Q009E5Q00102Q009D00A5009E000679009E00610001000D2Q0082012Q008C4Q0082012Q001F4Q0082012Q00914Q0082012Q00984Q0082012Q00994Q0082012Q00924Q0082012Q00954Q0082012Q008F4Q0082012Q00974Q0082012Q008E4Q0082012Q00904Q0082012Q00944Q0082012Q00933Q001037019D001B009E4Q009A009D000100122Q009A00013Q00202Q009A009A000200122Q009C00036Q009A009C000200202Q009A009A000500122Q009B00013Q00202Q009B009B000200122Q009D0094013Q0090009B009D0002002044019C009B003B00128E019E0095012Q00128E019F00B84Q0090009C009F000200069E009D00FE0601009C0004D03Q00FE0601002044019D009C003B00128E019F0096012Q00128E01A000B84Q0090009D00A0000200069E009E00040701009D0004D03Q00040701002044019E009D003B00128E01A00097012Q00128E01A100B84Q0090009E00A1000200069E009F000A0701009D0004D03Q000A0701002044019F009D003B00128E01A10098012Q00128E01A200B84Q0090009F00A2000200125701A000013Q00128E01A10099013Q00D100A000A000A100128E01A1009A012Q0006C500A00011070100A10004D03Q001107012Q003F01A06Q007100A000013Q00208000A10023008600202Q00A100A100E34Q00A33Q000200122Q00A4009B012Q00102Q00A3001200A400302Q00A300E500074Q00A100A3000100062Q00A0002407013Q0004D03Q002407010020CB00A1002300860020AF00A100A100E34Q00A33Q000200122Q00A4009C012Q00102Q00A3001200A400122Q00A4009D012Q00102Q00A300E500A42Q00A201A100A300010004D03Q00F1070100069E00A100280701009F0004D03Q0028070100128E01A1009E013Q00D100A1009F00A12Q009D01A200A23Q0012FD00A3007B012Q00122Q00A4009F015Q00A300A300A400122Q00A400A0012Q00122Q00A500076Q00A300A5000200122Q00A4007B012Q00122Q00A5009F015Q00A400A400A500122Q00A500A0012Q00128E01A600074Q006200A400A6000200122Q00A5007B012Q00122Q00A6009F015Q00A500A500A600122Q00A600A0015Q00A78Q00A500A700024Q00A68Q00A78Q00A800A83Q00022201A900623Q00067900AA0063000100042Q0082012Q00A24Q0082012Q00A84Q0082012Q009A4Q0082012Q00A93Q00067900AB0064000100032Q0082012Q00A24Q0082012Q00A44Q0082012Q00A13Q00060F009F007A07013Q0004D03Q007A070100060F009E007A07013Q0004D03Q007A070100128E01AC009E013Q00D100AC009F00AC00204401AC00AC006100067900AE0065000100022Q0082012Q00A84Q0082012Q00AB4Q00A201AC00AE00012Q009D01AC00AD3Q00125701AE00A1012Q00067900AF0066000100062Q0082012Q009E4Q0082012Q00A54Q0082012Q00A34Q0082012Q00A84Q0082012Q00AB4Q0082012Q00AD4Q00FC00AE000200AF2Q008201AD00AF4Q008201AC00AE3Q00065801AC006B070100010004D03Q006B070100128E01B000A2013Q000600AE001F00B04Q00B03Q000300122Q00B100A3012Q00102Q00B0001200B100122Q00B100A4012Q00102Q00B000E500B100122Q00B100183Q00102Q00B0001700B14Q00AE00B0000100128E01AE0096013Q00D100AE009A00AE00060F00AE007307013Q0004D03Q0073070100125701AE002F3Q0020CB00AE00AE00302Q008201AF00AA4Q009A00AE0002000100128E01AE0007013Q00D100AE009A00AE00204401AE00AE006100067900B00067000100012Q0082012Q00AA4Q00A201AE00B000012Q008001AC5Q00128E01AC00453Q00067900AD0068000100012Q0082012Q00AC3Q0020E000AE0023008600202Q00AE00AE00D200122Q00B000A5015Q00B13Q000500122Q00B200A6012Q00102Q00B1001200B200122Q00B200A7012Q00102Q00B100EE00B200122Q00B20048012Q00122Q00B30052013Q00E600B100B200B300128E01B20052012Q00107A00B100A500B200067900B20069000100032Q0082012Q00AC4Q0082012Q009A4Q0082012Q00AD3Q0010B600B1001B00B24Q00AE00B1000100122Q00AE0007015Q00AE009A00AE00202Q00AE00AE006100067900B0006A000100012Q0082012Q00AD4Q00A201AE00B0000100125701AE002F3Q0020CB00AE00AE003000067900AF006B000100032Q0082012Q009A4Q0082012Q00AC4Q0082012Q00AD4Q009A00AE0002000100128E01AE00453Q00128E01AF00A0012Q00128E01B000453Q0004CD00AE00B707010020CB00B20023008600203400B200B200D200122Q00B400A8015Q00B500B16Q00B400B400B54Q00B53Q000400122Q00B600A9015Q00B700B16Q00B600B600B700102Q00B5001200B600122Q00B60048012Q00128E01B700AA013Q00E600B500B600B700304C00B500A5000700067900B6006C000100022Q0082012Q00A34Q0082012Q00B13Q00107A00B5001B00B62Q009000B200B500022Q00E600A600B100B22Q008001B15Q0004F500AE00A1070100128E01AE00453Q00128E01AF00A0012Q00128E01B000453Q0004CD00AE00D107010020CB00B20023008600203400B200B200D200122Q00B400AB015Q00B500B16Q00B400B400B54Q00B53Q000400122Q00B600AC015Q00B700B16Q00B600B600B700102Q00B5001200B600122Q00B60048012Q00128E01B700AD013Q00E600B500B600B700304C00B500A5000700067900B6006D000100022Q0082012Q00A44Q0082012Q00B13Q00107A00B5001B00B62Q009000B200B500022Q00E600A700B100B22Q008001B15Q0004F500AE00BB07010020CB00AE002300860020AF00AE00AE00C24Q00B03Q000300122Q00B100AE012Q00102Q00B0001200B100122Q00B100AF012Q00102Q00B000EE00B100067900B1006E000100052Q0082012Q00A34Q0082012Q00A44Q0082012Q001F4Q0082012Q009B4Q0082012Q00A53Q00102600B0001B00B14Q00AE00B0000100202Q00AE0023008600202Q00AE00AE00C24Q00B03Q000300122Q00B100B0012Q00102Q00B0001200B100122Q00B100B1012Q00102Q00B000EE00B100067900B1006F000100062Q0082012Q00A34Q0082012Q00A44Q0082012Q00A54Q0082012Q00A64Q0082012Q00A74Q0082012Q001F3Q00107A00B0001B00B12Q00A201AE00B000012Q008001A15Q0020CB00A1002300860020F100A100A100E34Q00A33Q000200122Q00A400B2012Q00102Q00A3001200A400122Q00A400B3012Q00102Q00A300E500A44Q00A100A3000100062Q00A0004D08013Q0004D03Q004D08012Q008100A16Q007100A26Q007100A35Q00067900A40070000100052Q0082012Q009B4Q0082012Q00A34Q0082012Q00A24Q0082012Q009A4Q0082012Q00A14Q00B200A55Q00202Q00A6009B003D00122Q00A800B4015Q00A600A8000200062Q00A6001F08013Q0004D03Q001F080100204401A700A6003D00128E01A900B5013Q009000A700A9000200060F00A7001F08013Q0004D03Q001F080100125701A7007A012Q00125D01A800B5015Q00A800A600A800122Q00AA00B6015Q00A800A800AA4Q00A800A96Q00A73Q00A900044Q001D080100125701AC007B012Q00126F00AD007C015Q00AC00AC00AD4Q00AD00A53Q00202Q00AE00AB00144Q00AC00AE000100064801A70017080100020004D03Q0017080100128E01A700453Q00128E01A800B7012Q00128E01A900453Q0004CD00A7003C08010020CB00AB0023008600128E01AD000D013Q00AB01AB00AB00AD00128E01AD00B8013Q008201AE00AA4Q003B01AD00AD00AE2Q008100AE3Q000500128E01AF00B9013Q008201B000AA4Q003B01AF00AF00B000107A00AE001200AF00128E01AF0011013Q000200AE00AF00A500122Q00AF0080015Q00B08Q00AE00AF00B04Q00AF00AF3Q00102Q00AE00A500AF00067900AF0071000100022Q0082012Q00A14Q0082012Q00AA3Q00107A00AE001B00AF2Q00A201AB00AE00012Q008001AA5Q0004F500A7002308010020CB00A7002300860020AF00A700A700C24Q00A93Q000300122Q00AA00BA012Q00102Q00A9001200AA00122Q00AA00BB012Q00102Q00A900EE00AA00067900AA0072000100052Q0082012Q00A24Q0082012Q00A14Q0082012Q009A4Q0082012Q00A44Q0082012Q001F3Q00107A00A9001B00AA2Q00A201A700A900012Q008001A15Q0004D03Q005508010020CB00A1002300860020AF00A100A100E34Q00A33Q000200122Q00A400BC012Q00102Q00A3001200A400122Q00A400BD012Q00102Q00A300E500A42Q00A201A100A300012Q007100A15Q00127D01A200013Q00202Q00A200A2000200122Q00A400036Q00A200A4000200122Q00A300013Q00202Q00A300A3000200122Q00A500696Q00A300A5000200122Q00A400013Q00202Q00A400A4000200128E01A600934Q00A401A400A6000200202Q00A500A200054Q00A600A86Q00A95Q00122Q00AA00BE012Q00067900AB0073000100052Q0082012Q00A94Q0082012Q00A54Q0082012Q00A84Q0082012Q00A44Q0082012Q00AA3Q00202601AC0023008300202Q00AC00AC00A200122Q00AE00BF015Q00AF3Q000400122Q00B000C0012Q00102Q00AF001200B000122Q00B000C1012Q00102Q00AF00EE00B04Q00B05Q00102Q00AF00A500B000067900B00074000100082Q0082012Q00A14Q0082012Q001F4Q0082012Q00A64Q0082012Q00A74Q0082012Q00A34Q0082012Q00AB4Q0082012Q00A94Q0082012Q00A83Q00107000AF001B00B04Q00AC00AF00014Q00AC5Q00122Q00AD00013Q00202Q00AD00AD000200122Q00AF00036Q00AD00AF000200122Q00AE00013Q00202Q00AE00AE000200122Q00B000694Q009000AE00B0000200122F01AF00013Q00202Q00AF00AF000200122Q00B100936Q00AF00B1000200202Q00B000AD00054Q00B100B16Q00B28Q00B38Q00B400B63Q00122Q00B700C2012Q00067900B80075000100012Q0082012Q00B03Q00067900B90076000100012Q0082012Q00B03Q00067900BA0077000100022Q0082012Q00B04Q0082012Q00B73Q00202601BB0023008300202Q00BB00BB00A200122Q00BD00C3015Q00BE3Q000400122Q00BF00C4012Q00102Q00BE001200BF00122Q00BF00C5012Q00102Q00BE00EE00BF4Q00BF5Q00102Q00BE00A500BF00067900BF00780001000D2Q0082012Q00AC4Q0082012Q001F4Q0082012Q00B24Q0082012Q00B34Q0082012Q00B44Q0082012Q00B54Q0082012Q00AE4Q0082012Q00B64Q0082012Q00B94Q0082012Q00B14Q0082012Q00AF4Q0082012Q00B84Q0082012Q00BA3Q00107A00BE001B00BF2Q00A201BB00BE000100067900BB0079000100012Q0082012Q00234Q006C00BC00BB6Q00BC0001000100202Q00BC0023008800202Q00BC00BC00C24Q00BE3Q000300122Q00BF003D012Q00102Q00BE001200BF00122Q00BF00C6012Q00102Q00BE00EE00BF00022201BF007A3Q00102100BE001B00BF4Q00BC00BE000100122Q00BE00C7015Q00BC002000BE4Q00BE001F6Q00BC00BE000100122Q00BE00C7015Q00BC002100BE4Q00BE001F6Q00BC00BE000100128E01BE00C8013Q00AB01BC002100BE0020CB00BE0023008F2Q00A201BC00BE000100128E01BE00C9013Q00AB01BC002000BE0020CB00BE0023008F2Q00A201BC00BE000100128E01BE00CA013Q00AB01BC002200BE00128E01BE00454Q00A201BC00BE00012Q00BA3Q00013Q007B3Q00023Q0003103Q006964656E746966796578656375746F72030F3Q006765746578656375746F726E616D65000B3Q001257012Q00013Q000658012Q0007000100010004D03Q00070001001257012Q00023Q000658012Q0007000100010004D03Q00070001000222017Q00822Q016Q00A7000100014Q00CE00016Q00BA3Q00013Q00013Q00013Q0003073Q00556E6B6E6F776E00033Q00128E012Q00014Q00DD3Q00024Q00BA3Q00017Q000C3Q00031B3Q00436865636B204578656375746F722053752Q706F72742048657265030C3Q00736574636C6970626F617264030B3Q00746F636C6970626F617264031D3Q00682Q7470733A2Q2F646973636F72642E2Q672F63446E5552376D536E7703073Q00536574436F726503103Q0053656E644E6F74696669636174696F6E03053Q005469746C65030F3Q005665726575732058204E6F7469636503043Q005465787403143Q00436F7079204C696E6B2053752Q63652Q7366756C03083Q004475726174696F6E026Q00144001153Q002654012Q0014000100010004D03Q001400010012572Q0100023Q0006582Q010009000100010004D03Q000900010012572Q0100033Q0006582Q010009000100010004D03Q000900010002222Q016Q0082010200013Q001221010300046Q0002000200014Q00025Q00202Q00020002000500122Q000400066Q00053Q000300302Q00050007000800302Q00050009000A00302Q0005000B000C4Q0002000500012Q00BA3Q00013Q00018Q00014Q00BA3Q00017Q000A3Q00026Q00F03F026Q0008402Q033Q00536574030E3Q004C6F6164696E672053797374656D03063Q00737472696E672Q033Q0072657003013Q002E03043Q007461736B03043Q0077616974026Q00E03F001C4Q003A7Q00060F3Q001B00013Q0004D03Q001B000100128E012Q00013Q00128E2Q0100023Q00128E010200013Q0004CD3Q001A00012Q003A00045Q0006580104000B000100010004D03Q000B00010004D05Q00012Q003A00045Q00206500040004000300122Q000600043Q00122Q000700053Q00202Q00070007000600122Q000800076Q000900036Q0007000900024Q0006000600074Q00040006000100122Q000400083Q00202Q00040004000900122Q0005000A6Q0004000200010004F53Q000700010004D05Q00012Q00BA3Q00017Q00013Q0003073Q0044657374726F7900044Q003A7Q002044014Q00012Q009A3Q000200012Q00BA3Q00017Q00013Q0003043Q00506C617900074Q003A7Q00060F3Q000600013Q0004D03Q000600012Q003A3Q00013Q002044014Q00012Q009A3Q000200012Q00BA3Q00017Q00043Q0003043Q007461736B03043Q0077616974026Q004E4003053Q007063612Q6C000B3Q001257012Q00013Q0020CB5Q000200128E2Q0100034Q001F012Q0002000200060F3Q000A00013Q0004D03Q000A0001001257012Q00043Q0002222Q016Q009A3Q000200010004D05Q00012Q00BA3Q00013Q00013Q00093Q0003053Q007061697273030F3Q005469636B65744553505F5461626C6503063Q00506172656E7403043Q004C696E6503063Q0052656D6F76650003123Q004F726967696E616C506F7461746F44617461030D3Q004261636B757053746F72616765030C3Q004F726967696E616C4461746100383Q001257012Q00013Q0012572Q0100024Q00FC3Q000200020004D03Q0019000100060F0003000900013Q0004D03Q000900010020CB00050003000300065801050019000100010004D03Q00190001001257010500024Q00D100050005000300060F0005001700013Q0004D03Q00170001001257010500024Q00D10005000500030020CB00050005000400060F0005001700013Q0004D03Q00170001001257010500024Q00D10005000500030020CB0005000500040020440105000500052Q009A000500020001001257010500023Q00205A010500030006000648012Q0004000100020004D03Q00040001001257012Q00013Q0012572Q0100074Q00FC3Q000200020004D03Q0026000100060F0003002400013Q0004D03Q002400010020CB00050003000300065801050026000100010004D03Q00260001001257010500073Q00205A010500030006000648012Q001F000100020004D03Q001F0001001257012Q00013Q0012572Q0100083Q0020CB0001000100092Q00FC3Q000200020004D03Q0035000100060F0003003200013Q0004D03Q003200010020CB00050003000300065801050035000100010004D03Q00350001001257010500083Q0020CB00050005000900205A010500030006000648012Q002D000100020004D03Q002D00012Q00BA3Q00017Q000B3Q00028Q0003053Q007061697273030B3Q004765744368696C6472656E2Q033Q004973412Q033Q00536B79030A3Q0041746D6F73706865726503063Q00436C6F75647303063Q00536B79626F7803053Q007461626C6503063Q00696E7365727403053Q00436C6F6E6500274Q003A8Q005B7Q002654012Q0026000100010004D03Q00260001001257012Q00024Q0001000100013Q00202Q0001000100034Q000100029Q00000200044Q0024000100204401050004000400128E010700054Q00900005000700020006580105001E000100010004D03Q001E000100204401050004000400128E010700064Q00900005000700020006580105001E000100010004D03Q001E000100204401050004000400128E010700074Q00900005000700020006580105001E000100010004D03Q001E000100204401050004000400128E010700084Q009000050007000200060F0005002400013Q0004D03Q00240001001257010500093Q0020F300050005000A4Q00065Q00202Q00070004000B4Q000700086Q00053Q0001000648012Q000A000100020004D03Q000A00012Q00BA3Q00017Q00183Q0003063Q00697061697273030B3Q004765744368696C6472656E2Q033Q004973412Q033Q00536B79030A3Q0041746D6F73706865726503063Q00436C6F75647303073Q0044657374726F7903083Q004F726967696E616C03053Q00436C6F6E6503063Q00506172656E7403083Q00496E7374616E63652Q033Q006E657703043Q004E616D6503093Q005665726F7573536B79030D3Q00726278612Q73657469643A2Q2F03083Q00746F737472696E6703083Q00536B79626F78426B03083Q00536B79626F78446E03083Q00536B79626F78467403083Q00536B79626F784C6603083Q00536B79626F78527403083Q00536B79626F785570030E3Q0053756E416E67756C617253697A65028Q00013A3Q0012792Q0100016Q00025Q00202Q0002000200024Q000200036Q00013Q000300044Q0017000100204401060005000300128E010800044Q009000060008000200065801060015000100010004D03Q0015000100204401060005000300128E010800054Q009000060008000200065801060015000100010004D03Q0015000100204401060005000300128E010800064Q009000060008000200060F0006001700013Q0004D03Q001700010020440106000500072Q009A0006000200010006482Q010006000100020004D03Q00060001002654012Q0026000100080004D03Q002600010012572Q0100014Q003A000200014Q00FC0001000200030004D03Q002300010020440106000500092Q001F0106000200022Q003A00075Q00107A0006000A00070006482Q01001F000100020004D03Q001F00010004D03Q003900010012572Q01000B3Q0020172Q010001000C00122Q000200046Q00010002000200302Q0001000D000E00122Q0002000F3Q00122Q000300106Q00048Q0003000200024Q00020002000300102Q00010011000200102Q00010012000200102Q00010013000200102Q00010014000200102Q00010015000200102Q00010016000200302Q0001001700184Q00035Q00102Q0001000A00032Q00BA3Q00017Q00043Q0003113Q0043617074757265436F6E74726F2Q6C6572030C3Q00436C69636B42752Q746F6E3203073Q00566563746F72322Q033Q006E6577000D4Q003A7Q00060F3Q000C00013Q0004D03Q000C00012Q003A3Q00013Q00207E5Q00016Q000200016Q00013Q00206Q000200122Q000200033Q00202Q0002000200044Q000200019Q0000012Q00BA3Q00017Q00023Q0003093Q0048656172746265617403073Q00436F2Q6E65637400104Q003A00035Q0020CB00030003000100204401030003000200067900053Q0001000A2Q003A3Q00014Q0082012Q00014Q003A3Q00024Q0082017Q0082012Q00024Q003A3Q00034Q003A3Q00044Q003A3Q00054Q003A3Q00064Q003A3Q00074Q00A20103000500012Q00BA3Q00013Q00013Q00143Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F7450617274030C3Q00476574412Q7472696275746503063Q00446F776E656403093Q0049734B6579446F776E03043Q00456E756D03073Q004B6579436F6465030B3Q004C656674436F6E74726F6C03043Q006D6174682Q033Q006D696E03063Q00434672616D65030A3Q004C2Q6F6B566563746F7203163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F72332Q033Q006E657703013Q005803013Q005903013Q005A029Q00484Q003A7Q000658012Q0004000100010004D03Q000400012Q00BA3Q00014Q003A3Q00023Q0020CB5Q00012Q00A6012Q00014Q003A3Q00013Q00060F3Q000E00013Q0004D03Q000E00012Q003A3Q00013Q002044014Q000200128E010200034Q00903Q000200022Q00A6012Q00034Q00103Q00023Q00206Q000400122Q000200058Q0002000200064Q001C000100010004D03Q001C00012Q003A3Q00013Q00060F3Q001C00013Q0004D03Q001C00012Q003A3Q00013Q002044014Q000400128E010200054Q00903Q000200022Q00A6012Q00044Q003A3Q00043Q00060F3Q004500013Q0004D03Q004500012Q003A3Q00033Q00060F3Q004500013Q0004D03Q004500012Q003A3Q00053Q0020985Q000600122Q000200073Q00202Q00020002000800202Q0002000200096Q0002000200064Q004500013Q0004D03Q00450001001257012Q000A3Q00203E014Q000B4Q000100066Q000200076Q0001000100024Q000200088Q000200026Q00068Q00093Q00206Q000C00206Q000D4Q000100033Q00122Q0002000F3Q00202Q00020002001000202Q00033Q00114Q000400066Q0003000300044Q000400033Q00202Q00040004000E00202Q00040004001200202Q00053Q00134Q000600066Q0005000500064Q00020005000200102Q0001000E000200044Q0047000100128E012Q00144Q00A6012Q00064Q00BA3Q00017Q00103Q0003063Q00626F756E636503053Q00622Q6F737403063Q006C61756E636803043Q006A756D702Q033Q0070616403043Q0072616D7003083Q00706C6174666F726D03063Q00737472696E6703053Q006C6F77657203043Q004E616D6503053Q00706169727303043Q0066696E6403063Q00506172656E742Q033Q0049734103053Q004D6F64656C03063Q00466F6C646572013E4Q005B2Q0100073Q00122Q000200013Q00122Q000300023Q00122Q000400033Q00122Q000500043Q00122Q000600053Q00122Q000700063Q00122Q000800076Q000100070001001257010200083Q00208501020002000900202Q00033Q000A4Q00020002000200122Q0003000B6Q000400016Q00030002000500044Q0018000100204401080002000C2Q0082010A00074Q00900008000A000200060F0008001800013Q0004D03Q001800012Q0071000800014Q00DD000800023Q00064801030011000100020004D03Q001100010020CB00033Q000D00060F0003003B00013Q0004D03Q003B00010020CB00033Q000D00204401030003000E00128E0105000F4Q009000030005000200065801030029000100010004D03Q002900010020CB00033Q000D00204401030003000E00128E010500104Q009000030005000200060F0003003B00013Q0004D03Q003B0001001257010300083Q0020CB00030003000900208501043Q000D00202Q00040004000A4Q00030002000200122Q0004000B6Q000500016Q00040002000600044Q0039000100204401090003000C2Q0082010B00084Q00900009000B000200060F0009003900013Q0004D03Q003900012Q0071000900014Q00DD000900023Q00064801040032000100020004D03Q003200012Q007100036Q00DD000300024Q00BA3Q00017Q00023Q0003073Q005374652Q70656403073Q00436F2Q6E656374000B4Q003A7Q0020CB5Q0001002044014Q000200067900023Q000100052Q003A3Q00014Q003A3Q00024Q003A3Q00034Q003A3Q00044Q003A3Q00054Q00A2012Q000200012Q00BA3Q00013Q00013Q000F3Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403063Q004865616C7468028Q0003163Q00412Q73656D626C794C696E65617256656C6F6369747903013Q005903103Q00476574546F756368696E67506172747303053Q00706169727303073Q00566563746F72332Q033Q006E657703013Q005803013Q005A00474Q003A7Q000658012Q0004000100010004D03Q000400012Q00BA3Q00014Q003A3Q00013Q0020CB5Q000100069E0001000B00013Q0004D03Q000B00010020442Q013Q000200128E010300034Q009000010003000200069E0002001000013Q0004D03Q0010000100204401023Q000400128E010400054Q009000020004000200060F0001004600013Q0004D03Q0046000100060F0002004600013Q0004D03Q004600010020CB000300020006000E2C00070046000100030004D03Q004600010020CB0003000100080020CB0003000300092Q003A000400024Q003E000400043Q00064E00030046000100040004D03Q0046000100204401030001000A2Q00550103000200024Q00048Q00058Q000600033Q000E2Q00070034000100060004D03Q003400010012570106000B4Q0082010700034Q00FC0006000200080004D03Q002F00012Q003A000B00034Q0082010C000A4Q001F010B0002000200060F000B002F00013Q0004D03Q002F00012Q0071000500013Q0004D03Q0031000100064801060028000100020004D03Q0028000100065801050034000100010004D03Q003400012Q0071000400013Q00060F0004004600013Q0004D03Q004600010012570106000C3Q0020A400060006000D00202Q00070001000800202Q00070007000E00122Q000800073Q00202Q00090001000800202Q00090009000F4Q00060009000200122Q0007000C3Q00202Q00070007000D00122Q000800076Q000900043Q00122Q000A00076Q0007000A00024Q00060006000700102Q0001000800062Q00BA3Q00017Q000E3Q0003093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403093Q0049734B6579446F776E03043Q00456E756D03073Q004B6579436F646503053Q00537061636503043Q004A756D70030D3Q00466C2Q6F724D6174657269616C03083Q004D6174657269616C2Q033Q00416972030B3Q004368616E6765537461746503113Q0048756D616E6F696453746174655479706503073Q004A756D70696E6700244Q003A7Q000658012Q0004000100010004D03Q000400012Q00BA3Q00014Q003A3Q00013Q0020CB5Q000100069E0001000B00013Q0004D03Q000B00010020442Q013Q000200128E010300034Q009000010003000200060F0001002300013Q0004D03Q002300012Q003A000200023Q00206901020002000400122Q000400053Q00202Q00040004000600202Q0004000400074Q00020004000200062Q00020018000100010004D03Q001800010020CB00020001000800060F0002002300013Q0004D03Q002300010020CB000200010009001257010300053Q0020CB00030003000A0020CB00030003000B0006C500020023000100030004D03Q0023000100204401020001000C001257010400053Q0020CB00040004000D0020CB00040004000E2Q00A20102000400012Q00BA3Q00017Q00033Q0003043Q007461736B03043Q007761697403053Q007063612Q6C00103Q001257012Q00013Q0020CB5Q00022Q009F012Q0001000200060F3Q000F00013Q0004D03Q000F00012Q003A7Q00060F5Q00013Q0004D05Q0001001257012Q00033Q00067900013Q000100032Q003A3Q00014Q003A3Q00024Q003A8Q009A3Q000200010004D05Q00012Q00BA3Q00013Q00013Q00223Q0003093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F6964030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403063Q004865616C7468028Q00030D3Q0052617963617374506172616D732Q033Q006E6577031A3Q0046696C74657244657363656E64616E7473496E7374616E636573030A3Q0046696C7465725479706503043Q00456E756D03113Q005261796361737446696C7465725479706503073Q004578636C75646503093Q00776F726B737061636503073Q005261796361737403083Q00506F736974696F6E03073Q00566563746F7233026Q0010C0030D3Q00466C2Q6F724D6174657269616C03083Q004D6174657269616C2Q033Q0041697203063Q00434672616D65026Q00F83F03163Q00412Q73656D626C794C696E65617256656C6F6369747903013Q005803013Q005A030B3Q004368616E6765537461746503113Q0048756D616E6F696453746174655479706503073Q004A756D70696E6703043Q007461736B03053Q00737061776E03043Q0077616974029A5Q99B93F00534Q003A7Q0020CB5Q000100069E0001000700013Q0004D03Q000700010020442Q013Q000200128E010300034Q009000010003000200069E0002000C00013Q0004D03Q000C000100204401023Q000400128E010400054Q009000020004000200060F0002005200013Q0004D03Q0052000100060F0001005200013Q0004D03Q005200010020CB000300010006000E2C00070052000100030004D03Q00520001001257010300083Q0020400103000300094Q0003000100024Q000400016Q00058Q00040001000100107A0003000A00040012B10004000C3Q00202Q00040004000D00202Q00040004000E00102Q0003000B000400122Q0004000F3Q00202Q00040004001000202Q00060002001100122Q000700123Q00202Q00070007000900122Q000800073Q00122Q000900133Q00122Q000A00076Q0007000A00024Q000800036Q00040008000200062Q00040031000100010004D03Q003100010020CB0005000100140012570106000C3Q0020CB0006000600150020CB0006000600160006C500050052000100060004D03Q005200010020CB000500020017001250010600173Q00202Q00060006000900122Q000700073Q00122Q000800183Q00122Q000900076Q0006000900024Q00050005000600102Q00020017000500122Q000500123Q00202Q00050005000900202Q00060002001900202Q00060006001A4Q000700013Q00202Q00080002001900202Q00080008001B4Q00050008000200102Q00020019000500202Q00050001001C00122Q0007000C3Q00202Q00070007001D00202Q00070007001E4Q00050007000100122Q0005001F3Q00202Q00050005002000067900063Q000100022Q003A3Q00024Q0082012Q00014Q00A301050002000100122Q0005001F3Q00202Q00050005002100122Q000600226Q0005000200012Q00BA3Q00013Q00013Q00083Q0003043Q007469636B026Q00F03F030B3Q004368616E6765537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503083Q0046722Q6566612Q6C03043Q007461736B03043Q007761697400153Q001257012Q00014Q009F012Q000100020020A65Q00020012572Q0100014Q009F2Q010001000200064E0001001400013Q0004D03Q001400012Q003A00015Q00060F0001001400013Q0004D03Q001400012Q003A000100013Q00205700010001000300122Q000300043Q00202Q00030003000500202Q0003000300064Q00010003000100122Q000100073Q00202Q0001000100084Q00010001000100044Q000300012Q00BA3Q00017Q002B3Q0003073Q0044657374726F790003083Q00496E7374616E63652Q033Q006E657703093Q005363722Q656E47756903043Q004E616D6503093Q004D6F62696C65475549030A3Q005465787442752Q746F6E03043Q0053697A6503053Q005544696D32028Q00025Q00C05C40025Q0080464003083Q00506F736974696F6E026Q00E03F025Q00804CC0026Q0036C003103Q004261636B67726F756E64436F6C6F723303063Q00436F6C6F723303073Q0066726F6D524742025Q00406540025Q00E06F4003163Q004261636B67726F756E645472616E73706172656E6379026Q33D33F03043Q0054657874030A3Q0054657874436F6C6F7233026Q00F03F03043Q00466F6E7403043Q00456E756D030E3Q00536F7572636553616E73426F6C6403083Q005465787453697A65026Q002A40030F3Q004175746F42752Q746F6E436F6C6F72010003083Q0055495374726F6B6503093Q00546869636B6E652Q73027Q004003053Q00436F6C6F7203113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E656374030A3Q00496E707574426567616E030C3Q00496E7075744368616E676564030A3Q00496E707574456E64656402794Q003A00026Q00D1000200023Q00060F0002000E00013Q0004D03Q000E00012Q003A00026Q0052000200023Q00202Q0002000200014Q0002000200014Q00025Q00202Q00023Q00024Q000200016Q00038Q0002000200016Q00013Q001257010200033Q00206600020002000400122Q000300056Q000400016Q0002000400024Q00035Q00122Q000400076Q00030003000400102Q0002000600034Q00038Q00033Q000200122Q000300033Q00202Q00030003000400122Q000400086Q000500026Q00030005000200122Q0004000A3Q00202Q00040004000400122Q0005000B3Q00122Q0006000C3Q00122Q0007000B3Q00122Q0008000D6Q00040008000200102Q00030009000400122Q0004000A3Q00202Q00040004000400122Q0005000F3Q00122Q000600103Q00122Q0007000F3Q00122Q000800116Q00040008000200102Q0003000E000400122Q000400133Q00202Q00040004001400122Q0005000B3Q00122Q000600153Q00122Q000700166Q00040007000200102Q00030012000400302Q00030017001800102Q000300193Q00122Q000400133Q00202Q00040004000400122Q0005001B3Q00122Q0006001B3Q00122Q0007001B6Q00040007000200102Q0003001A000400122Q0004001D3Q00202Q00040004001C00202Q00040004001E00102Q0003001C000400302Q0003001F002000302Q00030021002200122Q000400033Q00202Q00040004000400122Q000500236Q000600036Q00040006000200302Q00040024002500122Q000500133Q00202Q00050005001400122Q000600163Q00122Q0007000B3Q00122Q0008000B6Q00050008000200102Q0004002600054Q00055Q00202Q00060003002700202Q00060006002800067900083Q000100042Q003A3Q00024Q0082012Q00054Q0082012Q00014Q0082012Q00044Q00A20106000800012Q009D010600093Q0020CB000A00030029002044010A000A0028000679000C0001000100042Q0082012Q00064Q0082012Q00084Q0082012Q00094Q0082012Q00034Q00A2010A000C00010020CB000A0003002A002044010A000A0028000679000C0002000100012Q0082012Q00074Q00A2010A000C00012Q003A000A00033Q0020CB000A000A002A002044010A000A0028000679000C0003000100052Q0082012Q00074Q0082012Q00064Q0082012Q00084Q0082012Q00034Q0082012Q00094Q00A2010A000C00012Q003A000A00033Q0020CB000A000A002B002044010A000A0028000679000C0004000100012Q0082012Q00064Q00A2010A000C00012Q00BA3Q00013Q00053Q00053Q0003053Q00436F6C6F7203063Q00436F6C6F723303073Q0066726F6D524742028Q00025Q00E06F40001C4Q0092019Q002Q000100016Q00019Q008Q00018Q00026Q000100018Q000200016Q00036Q000100013Q00060F0001001400013Q0004D03Q001400010012572Q0100023Q00200C00010001000300122Q000200043Q00122Q000300053Q00122Q000400046Q0001000400020006582Q01001A000100010004D03Q001A00010012572Q0100023Q00200C00010001000300122Q000200053Q00122Q000300043Q00122Q000400046Q00010004000200107A3Q000100012Q00BA3Q00017Q00053Q00030D3Q0055736572496E7075745479706503043Q00456E756D030C3Q004D6F75736542752Q746F6E3103053Q00546F75636803083Q00506F736974696F6E01143Q0020C700013Q000100122Q000200023Q00202Q00020002000100202Q00020002000300062Q0001000C000100020004D03Q000C00010020CB00013Q0001001257010200023Q0020CB0002000200010020CB00020002000400066D2Q010013000100020004D03Q001300012Q0071000100014Q003D2Q015Q00202Q00013Q00054Q000100016Q000100033Q00202Q0001000100054Q000100024Q00BA3Q00017Q00043Q00030D3Q0055736572496E7075745479706503043Q00456E756D030D3Q004D6F7573654D6F76656D656E7403053Q00546F756368010E3Q0020C700013Q000100122Q000200023Q00202Q00020002000100202Q00020002000300062Q0001000C000100020004D03Q000C00010020CB00013Q0001001257010200023Q0020CB0002000200010020CB00020002000400066D2Q01000D000100020004D03Q000D00012Q00A6017Q00BA3Q00017Q00073Q0003083Q00506F736974696F6E03053Q005544696D322Q033Q006E657703013Q005803053Q005363616C6503063Q004F2Q6673657403013Q0059011F4Q003A00015Q00066D012Q001E000100010004D03Q001E00012Q003A000100013Q00060F0001001E00013Q0004D03Q001E00010020CB00013Q00012Q007F010200026Q0001000100024Q000200033Q00122Q000300023Q00202Q0003000300034Q000400043Q00202Q00040004000400202Q0004000400054Q000500043Q00202Q00050005000400202Q00050005000600202Q0006000100044Q0005000500064Q000600043Q00202Q00060006000700202Q0006000600054Q000700043Q00202Q00070007000700202Q00070007000600202Q0008000100074Q0007000700084Q00030007000200102Q0002000100032Q00BA3Q00017Q00043Q00030D3Q0055736572496E7075745479706503043Q00456E756D030C3Q004D6F75736542752Q746F6E3103053Q00546F756368010F3Q0020C700013Q000100122Q000200023Q00202Q00020002000100202Q00020002000300062Q0001000C000100020004D03Q000C00010020CB00013Q0001001257010200023Q0020CB0002000200010020CB00020002000400066D2Q01000E000100020004D03Q000E00012Q007100016Q00A62Q016Q00BA3Q00017Q000A3Q002Q033Q0049734103053Q004D6F64656C03063Q004D6F7665546F03073Q00566563746F72332Q033Q006E657703013Q005803013Q005903013Q005A03083Q00426173655061727403083Q00506F736974696F6E00284Q003A7Q00060F3Q002700013Q0004D03Q002700012Q003A7Q002044014Q000100128E010200024Q00903Q0002000200060F3Q001600013Q0004D03Q001600012Q003A7Q00200B5Q000300122Q000200043Q00202Q0002000200054Q000300013Q00202Q0003000300064Q000400013Q00202Q0004000400074Q000500013Q00202Q0005000500084Q000200054Q0059014Q00010004D03Q002700012Q003A7Q002044014Q000100128E010200094Q00903Q0002000200060F3Q002700013Q0004D03Q002700012Q003A7Q0012962Q0100043Q00202Q0001000100054Q000200013Q00202Q0002000200064Q000300013Q00202Q0003000300074Q000400013Q00202Q0004000400084Q00010004000200104Q000A00012Q00BA3Q00017Q00013Q0003053Q007063612Q6C01073Q0012572Q0100013Q00067900023Q000100032Q0082017Q003A8Q003A3Q00014Q009A0001000200012Q00BA3Q00013Q00013Q00203Q0003063Q0069706169727303093Q00776F726B7370616365030E3Q0047657444657363656E64616E747303043Q004E616D65030A3Q00496E7669735061727473030E3Q00496E76697369626C6557612Q6C7303053Q00496E7669732Q033Q0049734103083Q004261736550617274030C3Q005472616E73706172656E6379026Q00F03F030A3Q0043616E436F2Q6C6964652Q0103043Q0057612Q6C030D3Q00496E76697369626C6557612Q6C03043Q00436C6970030B3Q004765744368696C6472656E03053Q007461626C6503063Q00696E73657274010003093Q0042617365706C61746503043Q0053697A6503013Q005903063Q004E6F7469667903053Q005469746C65030B3Q005665726F7573205761766503073Q00436F6E74656E7403183Q00496E76697369626C652077612Q6C732072656D6F7665642103083Q004475726174696F6E026Q00084003063Q00506172656E7403193Q00496E76697369626C652077612Q6C7320726573746F7265642100734Q003A7Q00060F3Q005D00013Q0004D03Q005D00012Q00818Q00EA3Q00013Q00124Q00013Q00122Q000100023Q00202Q0001000100034Q000100029Q00000200044Q005300010020CB00050004000400266A01050015000100050004D03Q001500010020CB00050004000400266A01050015000100060004D03Q001500010020CB00050004000400266A01050015000100070004D03Q001500012Q003F01056Q0071000500013Q00204401060004000800128E010800094Q009000060008000200060F0006002C00013Q0004D03Q002C00010020CB00060004000A0026540106002A0001000B0004D03Q002A00010020CB00060004000C0026540106002A0001000D0004D03Q002A00010020CB00060004000400266A0106002B0001000E0004D03Q002B00010020CB00060004000400266A0106002B0001000F0004D03Q002B00010020CB00060004000400266A0106002B000100100004D03Q002B00012Q003F01066Q0071000600013Q00060F0005004400013Q0004D03Q00440001001257010700013Q0020440108000400112Q002D000800094Q001301073Q00090004D03Q00410001002044010C000B000800128E010E00094Q0090000C000E000200060F000C004100013Q0004D03Q004100010020CB000C000B000C00060F000C004100013Q0004D03Q00410001001257010C00123Q002030000C000C00134Q000D00016Q000E000B6Q000C000E000100302Q000B000C001400064801070033000100020004D03Q003300010004D03Q0053000100060F0006005300013Q0004D03Q005300010020CB00070004000400266A01070053000100150004D03Q005300010020CB0007000400160020CB000700070017000E2C000B0053000100070004D03Q00530001001257010700123Q0020300007000700134Q000800016Q000900046Q00070009000100302Q0004000C0014000648012Q000B000100020004D03Q000B00012Q003A3Q00023Q0020DC5Q00184Q00023Q000300302Q00020019001A00302Q0002001B001C00302Q0002001D001E6Q0002000100044Q00720001001257012Q00014Q003A000100014Q00FC3Q000200020004D03Q0067000100060F0004006700013Q0004D03Q006700010020CB00050004001F00060F0005006700013Q0004D03Q0067000100304C0004000C000D000648012Q0061000100020004D03Q006100012Q00818Q00D43Q00018Q00023Q00206Q00184Q00023Q000300302Q00020019001A00302Q0002001B002000302Q0002001D001E6Q000200012Q00BA3Q00019Q002Q0001044Q003A00016Q002B0001000100012Q00A6012Q00014Q00BA3Q00019Q002Q0001044Q003A00016Q002B0001000100012Q00A6012Q00014Q00BA3Q00019Q002Q0001044Q003A00016Q002B0001000100012Q00A6012Q00014Q00BA3Q00019Q002Q0001044Q003A00016Q002B0001000100012Q00A6012Q00014Q00BA3Q00017Q001A3Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F6964030C3Q005573654A756D70506F77657203093Q004A756D70506F77657203043Q006D61746803043Q007371727403093Q00776F726B737061636503073Q0047726176697479027Q0040030A3Q004A756D70486569676874028Q0003043Q0067616D65030D3Q0053746172746572506C6179657203123Q004368617261637465724A756D70506F77657203163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F72332Q033Q006E657703013Q005803013Q005A030B3Q004368616E6765537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503073Q004A756D70696E6700384Q003A7Q000658012Q0004000100010004D03Q000400012Q00BA3Q00014Q003A3Q00013Q0020CB5Q000100069E0001000B00013Q0004D03Q000B00010020442Q013Q000200128E010300034Q009000010003000200069E0002001000013Q0004D03Q0010000100204401023Q000400128E010400054Q009000020004000200060F0001003700013Q0004D03Q0037000100060F0002003700013Q0004D03Q003700010020CB00030002000600060F0003001A00013Q0004D03Q001A00010020CB00030002000700065801030022000100010004D03Q00220001001257010300083Q00205900030003000900122Q0004000A3Q00202Q00040004000B00102Q0004000C000400202Q00050002000D4Q0004000400054Q000300020002002639000300270001000E0004D03Q002700010012570104000F3Q0020CB0004000400100020CB0003000400112Q003A000400024Q00B700040003000400122Q000500133Q00202Q00050005001400202Q00060001001200202Q0006000600154Q000700043Q00202Q00080001001200202Q0008000800164Q00050008000200102Q00010012000500202Q00050002001700122Q000700183Q00202Q00070007001900202Q00070007001A4Q0005000700012Q00BA3Q00019Q002Q0001074Q004D00018Q0001000100016Q00016Q000100026Q00028Q0001000200016Q00019Q002Q0001044Q003A00016Q002B0001000100012Q00A6012Q00014Q00BA3Q00019Q002Q0001044Q003A00016Q002B0001000100012Q00A6012Q00014Q00BA3Q00019Q002Q0001044Q003A00016Q002B0001000100012Q00A6012Q00014Q00BA3Q00019Q002Q0001044Q003A00016Q002B0001000100012Q00A6012Q00014Q00BA3Q00017Q00013Q0003053Q007063612Q6C00064Q003A8Q002B3Q00010001001257012Q00013Q0002222Q016Q009A3Q000200012Q00BA3Q00013Q00013Q001F3Q0003063Q0069706169727303093Q00776F726B7370616365030E3Q0047657444657363656E64616E747303043Q004E616D6503043Q0066696E6403063Q00436163747573030E3Q0046696E6446697273744368696C6403123Q005665726F7573436163747573486974626F7803073Q0044657374726F792Q033Q0049734103053Q004D6F64656C030E3Q00476574426F756E64696E67426F7803083Q00426173655061727403063Q00434672616D6503043Q0053697A6503083Q00496E7374616E63652Q033Q006E657703043Q005061727403073Q00566563746F723303013Q0058026Q00E03F03013Q005A028Q0003013Q0059027Q0040030C3Q005472616E73706172656E6379026Q00F03F03083Q00416E63686F7265642Q01030A3Q0043616E436F2Q6C69646503063Q00506172656E7400463Q0012513Q00013Q00122Q000100023Q00202Q0001000100034Q000100029Q00000200044Q004300010020CB00050004000400204401050005000500128E010700064Q009000050007000200060F0005004300013Q0004D03Q0043000100204401050004000700128E010700084Q009000050007000200060F0005001300013Q0004D03Q001300010020440106000500092Q009A0006000200012Q009D010600073Q00204401080004000A00128E010A000B4Q00900008000A000200060F0008001E00013Q0004D03Q001E000100204401080004000C2Q00FC0008000200092Q0082010700094Q0082010600083Q0004D03Q0026000100204401080004000A00128E010A000D4Q00900008000A000200060F0008002600013Q0004D03Q002600010020CB00080004000E0020CB00070004000F2Q0082010600083Q00060F0006004300013Q0004D03Q00430001001257010800103Q00208F01080008001100122Q000900126Q00080002000200302Q00080004000800122Q000900133Q00202Q00090009001100202Q000A0007001400202Q000A000A001500122Q000B00153Q00202Q000C0007001600202Q000C000C00154Q0009000C000200102Q0008000F000900122Q0009000E3Q00202Q00090009001100122Q000A00173Q00202Q000B0007001800202Q000B000B001900122Q000C00176Q0009000C00024Q00090006000900102Q0008000E000900302Q0008001A001B00302Q0008001C001D00302Q0008001E001D00102Q0008001F0004000648012Q0006000100020004D03Q000600012Q00BA3Q00017Q00013Q0003083Q0053657456616C756501074Q00152Q018Q0001000100014Q000100013Q00202Q0001000100014Q00038Q0001000300016Q00017Q00013Q0003083Q0053657456616C756501074Q00152Q018Q0001000100014Q000100013Q00202Q0001000100014Q00038Q0001000300016Q00017Q00013Q0003083Q0053657456616C756501074Q00152Q018Q0001000100014Q000100013Q00202Q0001000100014Q00038Q0001000300016Q00017Q00023Q00034Q0003053Q007063612Q6C010E4Q003A00016Q002B00010001000100060F3Q000D00013Q0004D03Q000D000100266A012Q000D000100010004D03Q000D00010012572Q0100023Q00067900023Q000100042Q003A3Q00014Q0082017Q003A3Q00024Q003A3Q00034Q009A0001000200012Q00BA3Q00013Q00013Q00103Q0003073Q0044657374726F7903043Q0067616D65030A3Q004765744F626A65637473030D3Q00726278612Q73657469643A2Q2F028Q00026Q00F03F03063Q00506172656E7403093Q00776F726B7370616365030A3Q004D616B654A6F696E747303063Q004E6F7469667903053Q005469746C65030B3Q005665726F7573205761766503073Q00436F6E74656E74030B3Q004D6170204C6F616465642103083Q004475726174696F6E026Q00084000214Q003A7Q00060F3Q000600013Q0004D03Q000600012Q003A7Q002044014Q00012Q009A3Q00020001001257012Q00023Q0020B05Q000300122Q000200046Q000300016Q0002000200036Q000200024Q00015Q000E2Q00050020000100010004D03Q002000010020CB00013Q00062Q00632Q018Q00015Q00122Q000200083Q00102Q0001000700024Q00015Q00202Q0001000100094Q0001000200014Q000100026Q0001000100014Q000100033Q00202Q00010001000A4Q00033Q000300302Q0003000B000C00302Q0003000D000E00302Q0003000F00104Q0001000300012Q00BA3Q00017Q00013Q0003013Q005801074Q006C2Q018Q0001000100014Q000100013Q00102Q000100016Q000100026Q0001000100016Q00017Q00013Q0003013Q005901074Q006C2Q018Q0001000100014Q000100013Q00102Q000100016Q000100026Q0001000100016Q00017Q00013Q0003013Q005A01074Q006C2Q018Q0001000100014Q000100013Q00102Q000100016Q000100026Q0001000100016Q00017Q00013Q0003073Q0044657374726F79000B4Q003A8Q002B3Q000100012Q003A3Q00013Q00060F3Q000A00013Q0004D03Q000A00012Q003A3Q00013Q002044014Q00012Q009A3Q000200012Q009D017Q00A6012Q00014Q00BA3Q00017Q00113Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403063Q00434672616D652Q033Q006E657703013Q005803013Q0059025Q00407F4003013Q005A03063Q004E6F7469667903053Q005469746C65030B3Q005665726F7573205761766503073Q00436F6E74656E74031E3Q0054656C65706F7274656420352Q302073747564732061626F7665206D617003083Q004475726174696F6E026Q00084003183Q00506C65617365206C6F61642061206D61702066697273742100294Q00479Q003Q000100016Q00013Q00206Q000100062Q0001000900013Q0004D03Q000900010020442Q013Q000200128E010300034Q009000010003000200060F0001002800013Q0004D03Q002800012Q003A000200023Q00060F0002002100013Q0004D03Q00210001001257010200043Q0020230002000200054Q000300033Q00202Q0003000300064Q000400033Q00202Q00040004000700202Q0004000400084Q000500033Q00202Q0005000500094Q00020005000200102Q0001000400024Q000200043Q00202Q00020002000A4Q00043Q000300302Q0004000B000C00302Q0004000D000E00302Q0004000F00104Q00020004000100044Q002800012Q003A000200043Q00206101020002000A4Q00043Q000300302Q0004000B000C00302Q0004000D001100302Q0004000F00104Q0002000400012Q00BA3Q00017Q00013Q00030B3Q00446F776E6564205375726600084Q003A8Q002B3Q000100012Q003A3Q00013Q00128E2Q0100013Q00067900023Q000100012Q003A3Q00024Q00A2012Q000200012Q00BA3Q00013Q00017Q0001024Q00A6017Q00BA3Q00017Q00013Q00030A3Q0045646765205472696D7000084Q003A8Q002B3Q000100012Q003A3Q00013Q00128E2Q0100013Q00067900023Q000100012Q003A3Q00024Q00A2012Q000200012Q00BA3Q00013Q00017Q0001024Q00A6017Q00BA3Q00017Q00013Q0003093Q004175746F204A756D7000084Q003A8Q002B3Q000100012Q003A3Q00013Q00128E2Q0100013Q00067900023Q000100012Q003A3Q00024Q00A2012Q000200012Q00BA3Q00013Q00017Q0001024Q00A6017Q00BA3Q00017Q00013Q00030B3Q004175746F20426F756E636500084Q003A8Q002B3Q000100012Q003A3Q00013Q00128E2Q0100013Q00067900023Q000100012Q003A3Q00024Q00A2012Q000200012Q00BA3Q00013Q00017Q0001024Q00A6017Q00BA3Q00017Q000B3Q0003063Q004E6F7469667903053Q005469746C6503083Q00566572657573205803073Q00436F6E74656E74031B3Q0052752Q6E696E67204C6167737769746368205B424554415D3Q2E03083Q004475726174696F6E026Q000840030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403723Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F61646977706961736F702Q647761373866617364376173366431763661343877613776736164762F4C61677377697463682D424554412D2F726566732F68656164732F6D61696E2F6D61696E2E6C756100114Q00749Q003Q000100016Q00013Q00206Q00014Q00023Q000300302Q00020002000300302Q00020004000500302Q0002000600076Q0002000100124Q00083Q00122Q000100093Q00202Q00010001000A00122Q0003000B6Q000100039Q0000026Q000100016Q00017Q000B3Q0003063Q004E6F7469667903053Q005469746C6503083Q00566572657573205803073Q00436F6E74656E7403153Q0052752Q6E696E6720576174657220446173683Q2E03083Q004475726174696F6E026Q000840030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q7470476574036C3Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F61646977706961736F702Q647761373866617364376173366431763661343877613776736164762F57617465722D4D61702F726566732F68656164732F6D61696E2F6D61696E2E6C756100114Q00749Q003Q000100016Q00013Q00206Q00014Q00023Q000300302Q00020002000300302Q00020004000500302Q0002000600076Q0002000100124Q00083Q00122Q000100093Q00202Q00010001000A00122Q0003000B6Q000100039Q0000026Q000100016Q00017Q000B3Q0003063Q004E6F7469667903053Q005469746C6503083Q00566572657573205803073Q00436F6E74656E7403183Q0052752Q6E696E672042617365706C617465204D61703Q2E03083Q004475726174696F6E026Q000840030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403703Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F61646977706961736F702Q647761373866617364376173366431763661343877613776736164762F42617365706C6174652D4D61702F726566732F68656164732F6D61696E2F6D61696E2E6C756100114Q00749Q003Q000100016Q00013Q00206Q00014Q00023Q000300302Q00020002000300302Q00020004000500302Q0002000600076Q0002000100124Q00083Q00122Q000100093Q00202Q00010001000A00122Q0003000B6Q000100039Q0000026Q000100016Q00017Q000B3Q0003063Q004E6F7469667903053Q005469746C6503083Q00566572657573205803073Q00436F6E74656E7403153Q0052752Q6E696E6720544153205363726970743Q2E03083Q004475726174696F6E026Q000840030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q7470476574036D3Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F61646977706961736F702Q647761373866617364376173366431763661343877613776736164762F5441532D5363726970742F726566732F68656164732F6D61696E2F6D61696E2E6C756100114Q00749Q003Q000100016Q00013Q00206Q00014Q00023Q000300302Q00020002000300302Q00020004000500302Q0002000600076Q0002000100124Q00083Q00122Q000100093Q00202Q00010001000A00122Q0003000B6Q000100039Q0000026Q000100016Q00017Q000B3Q0003063Q004E6F7469667903053Q005469746C6503083Q00566572657573205803073Q00436F6E74656E74031C3Q0052752Q6E696E672046722Q6563616D205B53484946542B505D3Q2E03083Q004475726174696F6E026Q000840030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403213Q00682Q7470733A2Q2F706173746562696E2E636F6D2F7261772F4758364D79744A6D00114Q00749Q003Q000100016Q00013Q00206Q00014Q00023Q000300302Q00020002000300302Q00020004000500302Q0002000600076Q0002000100124Q00083Q00122Q000100093Q00202Q00010001000A00122Q0003000B6Q000100039Q0000026Q000100016Q00017Q000B3Q0003063Q004E6F7469667903053Q005469746C6503083Q00566572657573205803073Q00436F6E74656E7403173Q0052752Q6E696E672041696D626F74202D204553503Q2E03083Q004475726174696F6E026Q000840030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403533Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F53756E3036372F4553502D41696D626F742D62792D7369772F726566732F68656164732F6D61696E2F6D61696E2E6C756100114Q00749Q003Q000100016Q00013Q00206Q00014Q00023Q000300302Q00020002000300302Q00020004000500302Q0002000600076Q0002000100124Q00083Q00122Q000100093Q00202Q00010001000A00122Q0003000B6Q000100039Q0000026Q000100016Q00017Q000B3Q0003063Q004E6F7469667903053Q005469746C6503083Q00566572657573205803073Q00436F6E74656E74031A3Q0052752Q6E696E672050736861646520556C74696D6174653Q2E03083Q004475726174696F6E026Q000840030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403513Q00682Q7470733A2Q2F726177736372697074732E6E65742F7261772F556E6976657273616C2D5363726970742D5053686164652D556C74696D6174652D6E6F742D6D6164652D62792D6D652D31333833313500114Q00749Q003Q000100016Q00013Q00206Q00014Q00023Q000300302Q00020002000300302Q00020004000500302Q0002000600076Q0002000100124Q00083Q00122Q000100093Q00202Q00010001000A00122Q0003000B6Q000100039Q0000026Q000100016Q00017Q000B3Q0003063Q004E6F7469667903053Q005469746C6503083Q00566572657573205803073Q00436F6E74656E7403123Q0052752Q6E696E672053697720436F72652Q2E03083Q004475726174696F6E026Q000840030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q7470476574036A3Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F61646977706961736F702Q647761373866617364376173366431763661343877613776736164762F5369772D436F72652F726566732F68656164732F6D61696E2F7369772E6C756100114Q00749Q003Q000100016Q00013Q00206Q00014Q00023Q000300302Q00020002000300302Q00020004000500302Q0002000600076Q0002000100124Q00083Q00122Q000100093Q00202Q00010001000A00122Q0003000B6Q000100039Q0000026Q000100016Q00017Q000B3Q0003063Q004E6F7469667903053Q005469746C6503083Q00566572657573205803073Q00436F6E74656E7403183Q0052752Q6E696E6720417661746172204368616E6765722Q2E03083Q004475726174696F6E026Q000840030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403553Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F6461726B64657876322F756E6976657273616C6176617461726368616E6765722F6D61696E2F6176617461726368616E67657200114Q00749Q003Q000100016Q00013Q00206Q00014Q00023Q000300302Q00020002000300302Q00020004000500302Q0002000600076Q0002000100124Q00083Q00122Q000100093Q00202Q00010001000A00122Q0003000B6Q000100039Q0000026Q000100016Q00017Q000B3Q0003063Q004E6F7469667903053Q005469746C6503083Q00566572657573205803073Q00436F6E74656E7403163Q0052752Q6E696E67205368616465722045766164652Q2E03083Q004475726174696F6E026Q000840030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403673Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F61646977706961736F702Q647761373866617364376173366431763661343877613776736164762F746573742F726566732F68656164732F6D61696E2F6D61696E2E6C756100114Q00749Q003Q000100016Q00013Q00206Q00014Q00023Q000300302Q00020002000300302Q00020004000500302Q0002000600076Q0002000100124Q00083Q00122Q000100093Q00202Q00010001000A00122Q0003000B6Q000100039Q0000026Q000100016Q00017Q000B3Q0003063Q004E6F7469667903053Q005469746C6503083Q00566572657573205803073Q00436F6E74656E7403193Q0052752Q6E696E6720496E66696E697465205969656C643Q2E03083Q004475726174696F6E026Q000840030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403443Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F4564676549592F696E66696E6974657969656C642F6D61737465722F736F7572636500114Q00749Q003Q000100016Q00013Q00206Q00014Q00023Q000300302Q00020002000300302Q00020004000500302Q0002000600076Q0002000100124Q00083Q00122Q000100093Q00202Q00010001000A00122Q0003000B6Q000100039Q0000026Q000100016Q00017Q00143Q0003083Q00497341637469766503053Q00706169727303093Q00776F726B7370616365030E3Q0047657444657363656E64616E747303043Q0067616D6503073Q00506C6179657273030A3Q00476574506C617965727303093Q00436861726163746572030E3Q00497344657363656E64616E744F662Q033Q0049734103083Q004261736550617274030C3Q004F726967696E616C446174612Q033Q00436F6C03053Q00436F6C6F722Q033Q00547261030C3Q005472616E73706172656E637903043Q007461736B03053Q00737061776E03053Q007461626C6503053Q00636C65617201514Q003A00015Q0020CB00010001000100066D012Q0005000100010004D03Q000500012Q00BA3Q00014Q003A00015Q00107A000100013Q00060F3Q003A00013Q0004D03Q003A00010012572Q0100023Q001246000200033Q00202Q0002000200044Q000200036Q00013Q000300044Q003700012Q007100065Q0012BD000700023Q00122Q000800053Q00202Q00080008000600202Q0008000800074Q000800096Q00073Q000900044Q002100010020CB000C000B000800060F000C002100013Q0004D03Q00210001002044010C000500090020CB000E000B00082Q0090000C000E000200060F000C002100013Q0004D03Q002100012Q0071000600013Q0004D03Q0023000100064801070017000100020004D03Q0017000100065801060037000100010004D03Q0037000100204401070005000A00128E0109000B4Q009000070009000200060F0007003700013Q0004D03Q003700012Q003A00075Q0020CB00070007000C2Q00D100070007000500065801070037000100010004D03Q003700012Q003A00075Q00205F01070007000C4Q00083Q000200202Q00090005000E00102Q0008000D000900202Q00090005001000102Q0008000F00094Q0007000500080006482Q01000F000100020004D03Q000F00010004D03Q005000010012572Q0100024Q003A00025Q0020CB00020002000C2Q00FC0001000200030004D03Q00460001001257010600113Q0020CB00060006001200067900073Q000100022Q0082012Q00044Q0082012Q00054Q009A0006000200012Q008001045Q0006482Q01003F000100020004D03Q003F00010012572Q0100133Q00207A2Q01000100144Q00025Q00202Q00020002000C4Q0001000200014Q00018Q00025Q00102Q0001000C00022Q00BA3Q00013Q00013Q00013Q0003053Q007063612Q6C00063Q001257012Q00013Q00067900013Q000100022Q003A8Q003A3Q00014Q009A3Q000200012Q00BA3Q00013Q00013Q00053Q0003063Q00506172656E7403053Q00436F6C6F722Q033Q00436F6C030C3Q005472616E73706172656E63792Q033Q0054726100104Q003A7Q00060F3Q000F00013Q0004D03Q000F00012Q003A7Q0020CB5Q000100060F3Q000F00013Q0004D03Q000F00012Q003A8Q00B3000100013Q00202Q00010001000300104Q000200019Q004Q000100013Q00202Q00010001000500104Q000400012Q00BA3Q00017Q00053Q00030C3Q0057616974466F724368696C6403043Q0048656164026Q00144003043Q007461736B03053Q00737061776E01113Q000658012Q0003000100010004D03Q000300012Q00BA3Q00013Q0020442Q013Q000100128E010300023Q00128E010400034Q009000010004000200060F0001001000013Q0004D03Q00100001001257010200043Q0020CB00020002000500067900033Q000100032Q003A8Q0082017Q0082012Q00014Q009A0002000200012Q00BA3Q00013Q00013Q000C3Q0003083Q00486561646C652Q7303063Q00506172656E74030C3Q005472616E73706172656E6379026Q00F03F03053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q00446563616C03073Q005465787475726503043Q007461736B03043Q0077616974026Q00E03F002A4Q003A7Q0020CB5Q000100060F3Q002900013Q0004D03Q002900012Q003A3Q00013Q00060F3Q002900013Q0004D03Q002900012Q003A3Q00013Q0020CB5Q000200060F3Q002900013Q0004D03Q002900012Q003A3Q00023Q0020CB5Q000200060F3Q002900013Q0004D03Q002900012Q003A3Q00023Q00304C3Q00030004001279012Q00056Q000100023Q00202Q0001000100064Q000100029Q00000200044Q0022000100204401050004000700128E010700084Q009000050007000200065801050021000100010004D03Q0021000100204401050004000700128E010700094Q009000050007000200060F0005002200013Q0004D03Q0022000100304C000400030004000648012Q0017000100020004D03Q00170001001257012Q000A3Q0020CB5Q000B00128E2Q01000C4Q009A3Q000200010004D05Q00012Q00BA3Q00017Q00023Q0003043Q007461736B03053Q00737061776E010D3Q000658012Q0003000100010004D03Q000300012Q00BA3Q00013Q0012572Q0100013Q0020CB00010001000200067900023Q000100052Q003A8Q0082017Q003A3Q00014Q003A3Q00024Q003A3Q00034Q009A0001000200012Q00BA3Q00013Q00013Q001C3Q0003073Q004B6F72626C6F7803063Q00506172656E74030E3Q0046696E6446697273744368696C6403093Q005269676874204C6567030B3Q004B6F72626C6F784D65736803083Q00496E7374616E63652Q033Q006E6577030D3Q004368617261637465724D65736803043Q004E616D6503083Q00426F64795061727403043Q00456E756D03083Q0052696768744C656703063Q004D6573684964030D3Q0042617365546578747572654964028Q0003103Q004F7665726C617954657874757265496403063Q00697061697273030B3Q004765744368696C6472656E2Q033Q00497341030B3Q005370656369616C4D65736803073Q0044657374726F7903053Q00436F6C6F72030C3Q005472616E73706172656E637903083Q004D6174657269616C03073Q00506C617374696303043Q007461736B03043Q0077616974029A5Q99C93F00534Q003A7Q0020CB5Q000100060F3Q005200013Q0004D03Q005200012Q003A3Q00013Q00060F3Q005200013Q0004D03Q005200012Q003A3Q00013Q0020CB5Q000200060F3Q005200013Q0004D03Q005200012Q003A3Q00013Q002044014Q000300128E010200044Q00903Q0002000200060F3Q004D00013Q0004D03Q004D00012Q003A000100013Q0020442Q010001000300128E010300054Q00900001000300020006582Q010029000100010004D03Q00290001001257010200063Q00203001020002000700122Q000300086Q0002000200024Q000100023Q00302Q00010009000500122Q0002000B3Q00202Q00020002000A00202Q00020002000C00102Q0001000A00024Q000200023Q00102Q0001000D000200302Q0001000E000F4Q000200033Q00102Q0001001000024Q000200013Q00102Q00010002000200044Q002B00012Q003A000200023Q00107A0001000D0002001257010200113Q00204401033Q00122Q002D000300044Q001301023Q00040004D03Q0037000100204401070006001300128E010900144Q009000070009000200060F0007003700013Q0004D03Q003700010020440107000600152Q009A00070002000100064801020030000100020004D03Q003000010020CB00023Q00162Q003A000300043Q0006C50002003F000100030004D03Q003F00012Q003A000200043Q00107A3Q001600020020CB00023Q001700266A010200430001000F0004D03Q0043000100304C3Q0017000F0020CB00023Q00180012570103000B3Q0020CB0003000300180020CB0003000300190006C50002004D000100030004D03Q004D00010012570102000B3Q0020CB0002000200180020CB00020002001900107A3Q001800020012572Q01001A3Q0020CB00010001001B00128E0102001C4Q009A0001000200010004D05Q00012Q00BA3Q00017Q00053Q0003043Q007461736B03043Q0077616974026Q00E03F03083Q00486561646C652Q7303073Q004B6F72626C6F7801133Q00128B000100013Q00202Q00010001000200122Q000200036Q0001000200014Q00015Q00202Q00010001000400062Q0001000B00013Q0004D03Q000B00012Q003A000100014Q008201026Q009A0001000200012Q003A00015Q0020CB00010001000500060F0001001200013Q0004D03Q001200012Q003A000100024Q008201026Q009A0001000200012Q00BA3Q00017Q000A3Q0003083Q00486561646C652Q732Q0103093Q0043686172616374657203063Q004E6F7469667903053Q005469746C65030B3Q005665726F7573205761766503073Q00436F6E74656E7403113Q00486561646C652Q7320412Q706C6965642103083Q004475726174696F6E026Q00084000104Q001D019Q002Q000100016Q00013Q00304Q000100026Q00026Q000100033Q00202Q0001000100036Q000200016Q00043Q00206Q00044Q00023Q000300302Q00020005000600302Q00020007000800302Q00020009000A6Q000200016Q00017Q000A3Q0003073Q004B6F72626C6F782Q0103093Q0043686172616374657203063Q004E6F7469667903053Q005469746C65030B3Q005665726F7573205761766503073Q00436F6E74656E7403103Q004B6F72626C6F7820412Q706C6965642103083Q004475726174696F6E026Q00084000104Q001D019Q002Q000100016Q00013Q00304Q000100026Q00026Q000100033Q00202Q0001000100036Q000200016Q00043Q00206Q00044Q00023Q000300302Q00020005000600302Q00020007000800302Q00020009000A6Q000200016Q00017Q00163Q0003083Q00486561646C652Q73010003073Q004B6F72626C6F7803093Q00436861726163746572030E3Q0046696E6446697273744368696C64030B3Q004B6F72626C6F784D65736803073Q0044657374726F7903043Q0048656164030C3Q005472616E73706172656E6379028Q0003053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q00446563616C03073Q005465787475726503063Q004E6F7469667903053Q005469746C65030B3Q005665726F7573205761766503073Q00436F6E74656E74031E3Q00436861726163746572204D6F64696669636174696F6E732052657365742103083Q004475726174696F6E026Q00084000314Q00A59Q003Q000100016Q00013Q00304Q000100026Q00013Q00304Q000300026Q00023Q00206Q000400064Q002900013Q0004D03Q002900010020442Q013Q000500128E010300064Q009000010003000200060F0001001100013Q0004D03Q001100010020440102000100072Q009A00020002000100204401023Q000500128E010400084Q009000020004000200060F0002002900013Q0004D03Q0029000100304C00020009000A0012460003000B3Q00202Q00040002000C4Q000400056Q00033Q000500044Q0027000100204401080007000D00128E010A000E4Q00900008000A000200065801080026000100010004D03Q0026000100204401080007000D00128E010A000F4Q00900008000A000200060F0008002700013Q0004D03Q0027000100304C00070009000A0006480103001C000100020004D03Q001C00012Q003A000100033Q0020612Q01000100104Q00033Q000300302Q00030011001200302Q00030013001400302Q0003001500164Q0001000300012Q00BA3Q00017Q000B3Q0003083Q004F726967696E616C030D3Q00507572706C65204E6562756C61023Q00B62802A34103093Q004E6967687420536B79023Q0060AD02674103063Q0053756E736574023Q00A865E8C14103083Q00426C756520536B79023Q006E6952A24103063Q0047616C617879023Q007E2802A34101264Q003A00016Q002B000100010001002654012Q0008000100010004D03Q000800012Q003A000100013Q00128E010200014Q009A0001000200010004D03Q00250001002654012Q000E000100020004D03Q000E00012Q003A000100013Q00128E010200034Q009A0001000200010004D03Q00250001002654012Q0014000100040004D03Q001400012Q003A000100013Q00128E010200054Q009A0001000200010004D03Q00250001002654012Q001A000100060004D03Q001A00012Q003A000100013Q00128E010200074Q009A0001000200010004D03Q00250001002654012Q0020000100080004D03Q002000012Q003A000100013Q00128E010200094Q009A0001000200010004D03Q00250001002654012Q00250001000A0004D03Q002500012Q003A000100013Q00128E0102000B4Q009A0001000200012Q00BA3Q00017Q00083Q0003083Q004F726967696E616C03063Q004E6F7469667903053Q005469746C65030B3Q00536B79204368616E67657203073Q00436F6E74656E7403153Q00526573746F726564206F726967696E616C20736B7903083Q004475726174696F6E026Q000840000D4Q0088019Q002Q000100016Q00013Q00122Q000100018Q000200016Q00023Q00206Q00024Q00023Q000300302Q00020003000400302Q00020005000600302Q0002000700086Q000200016Q00017Q00023Q00034Q0003053Q007063612Q6C01104Q003A00016Q002B00010001000100060F3Q000F00013Q0004D03Q000F000100266A012Q000F000100010004D03Q000F00010012572Q0100023Q00067900023Q000100062Q0082017Q003A3Q00014Q003A3Q00024Q003A3Q00034Q003A3Q00044Q003A3Q00054Q009A0001000200012Q00BA3Q00013Q00013Q00303Q00030D3Q00726278612Q73657469643A2Q2F03093Q00776F726B7370616365030E3Q0046696E6446697273744368696C64030C3Q00437573746F6D536B79626F7803073Q0044657374726F7903083Q00496E7374616E63652Q033Q006E657703043Q005061727403043Q004E616D6503043Q0053697A6503073Q00566563746F7233025Q00408F4003053Q00536861706503043Q00456E756D03083Q00506172745479706503043Q0042612Q6C030C3Q005472616E73706172656E6379028Q00030A3Q0043616E436F2Q6C696465010003083Q0043616E5175657279030A3Q0043617374536861646F7703083Q00416E63686F7265642Q0103063Q00506172656E74030B3Q005370656369616C4D65736803083Q004D6573685479706503063Q0053706865726503053Q005363616C65025Q00408FC003093Q00546578747572654964030A3Q00446973636F2Q6E656374030D3Q0052656E6465725374652Q70656403073Q00436F2Q6E65637403063Q00466F67456E64025Q006AF84003153Q0046696E6446697273744368696C644F66436C612Q73030A3Q0041746D6F7370686572650003053Q007072696E7403133Q00437573746F6D20536B793A20454E41424C454403063Q004E6F7469667903053Q005469746C65030B3Q005665726F7573205761766503073Q00436F6E74656E7403153Q00437573746F6D20536B79626F78204C6F616465642103083Q004475726174696F6E026Q00084000593Q00128E012Q00014Q003A00016Q003B014Q00010012B9000100023Q00202Q00010001000300122Q000300046Q00010003000200062Q0001000B00013Q0004D03Q000B00010020440102000100052Q009A000200020001001257010200063Q0020CB00020002000700128E010300084Q001F01020002000200304C0002000900040012760003000B3Q00202Q00030003000700122Q0004000C3Q00122Q0005000C3Q00122Q0006000C6Q00030006000200102Q0002000A00030012380003000E3Q00202Q00030003000F00202Q00030003001000102Q0002000D000300302Q00020011001200302Q00020013001400302Q00020015001400302Q00020016001400302Q00020017001800122Q000300023Q00107A00020019000300125C010300063Q00202Q00030003000700122Q0004001A6Q00030002000200122Q0004000E3Q00202Q00040004001B00202Q00040004001C00102Q0003001B00040012760004000B3Q00202Q00040004000700122Q0005001E3Q00122Q0006001E3Q00122Q0007001E6Q00040007000200102Q0003001D000400107A0003001F3Q00107A0003001900022Q003A000400013Q00060F0004003900013Q0004D03Q003900012Q003A000400013Q0020440104000400202Q009A0004000200012Q003A000400023Q0020CB00040004002100204401040004002200067900063Q000100022Q0082012Q00024Q003A3Q00034Q000B0104000600024Q000400016Q000400043Q00302Q0004002300244Q000400043Q00202Q00040004002500122Q000600266Q00040006000200062Q0004004E00013Q0004D03Q004E00012Q003A000400043Q00204401040004002500128E010600264Q009000040006000200304C000400190027001257010400283Q001239010500296Q0004000200014Q000400053Q00202Q00040004002A4Q00063Q000300302Q0006002B002C00302Q0006002D002E00302Q0006002F00304Q0004000600016Q00013Q00013Q00033Q0003063Q00434672616D652Q033Q006E657703083Q00506F736974696F6E000C4Q003A7Q00060F3Q000B00013Q0004D03Q000B00012Q003A7Q0012D9000100013Q00202Q0001000100024Q000200013Q00202Q00020002000100202Q0002000200034Q00010002000200104Q000100012Q00BA3Q00017Q00013Q0003053Q007063612Q6C00094Q003A8Q002B3Q00010001001257012Q00013Q00067900013Q000100032Q003A3Q00014Q003A3Q00024Q003A3Q00034Q009A3Q000200012Q00BA3Q00013Q00013Q00183Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C64030F3Q00416C7961506572736F6E616C536B7903073Q0044657374726F79030C3Q00437573746F6D536B79626F7803063Q00466F67456E64025Q0088C34003083Q00466F675374617274028Q0003153Q0046696E6446697273744368696C644F66436C612Q73030A3Q0041746D6F73706865726503083Q00496E7374616E63652Q033Q006E657703063Q00506172656E74030A3Q00446973636F2Q6E65637403053Q007072696E7403173Q00437573746F6D20536B79626F783A2044495341424C454403063Q004E6F7469667903053Q005469746C65030B3Q005665726F7573205761766503073Q00436F6E74656E7403173Q00437573746F6D20536B79626F782044697361626C65642103083Q004475726174696F6E026Q00084000313Q0012B93Q00013Q00206Q000200122Q000200038Q0002000200064Q000800013Q0004D03Q000800010020442Q013Q00042Q009A0001000200010012572Q0100013Q0020442Q010001000200128E010300054Q009000010003000200060F0001001000013Q0004D03Q001000010020440102000100042Q009A0002000200012Q003A00025Q00309B0102000600074Q00025Q00302Q0002000800094Q00025Q00202Q00020002000A00122Q0004000B6Q00020004000200062Q00020020000100010004D03Q002000010012570102000C3Q0020CB00020002000D00128E0103000B4Q001F0102000200022Q003A00035Q00107A0002000E00032Q003A000200013Q00060F0002002600013Q0004D03Q002600012Q003A000200013Q00204401020002000F2Q009A000200020001001257010200103Q001239010300116Q0002000200014Q000200023Q00202Q0002000200124Q00043Q000300302Q00040013001400302Q00040015001600302Q0004001700184Q0002000400016Q00019Q002Q0001044Q003A00016Q002B0001000100012Q00A6012Q00014Q00BA3Q00017Q00093Q0003073Q00416D6269656E74030E3Q004F7574642Q6F72416D6269656E74030A3Q004272696768746E652Q7303093Q00436C6F636B54696D6503063Q00466F67456E64030D3Q00476C6F62616C536861646F7773030A3Q00446973636F2Q6E65637403073Q004368616E67656403073Q00436F2Q6E65637401524Q003A00016Q002B00010001000100060F3Q002D00013Q0004D03Q002D00012Q003A000100014Q00B3000200023Q00202Q00020002000100102Q0001000100024Q000100016Q000200023Q00202Q00020002000200102Q0001000200022Q003A000100014Q00B3000200023Q00202Q00020002000300102Q0001000300024Q000100016Q000200023Q00202Q00020002000400102Q0001000400022Q003A000100014Q00B3000200023Q00202Q00020002000500102Q0001000500024Q000100016Q000200023Q00202Q00020002000600102Q00010006000200067900013Q000100012Q003A3Q00024Q0082010200014Q002B0002000100012Q003A000200033Q00060F0002002600013Q0004D03Q002600012Q003A000200033Q0020440102000200072Q009A0002000200012Q003A000200023Q00200701020002000800202Q0002000200094Q000400016Q0002000400024Q000200033Q00044Q005100012Q003A000100033Q00060F0001003500013Q0004D03Q003500012Q003A000100033Q0020442Q01000100072Q009A0001000200012Q009D2Q0100014Q00A62Q0100034Q003A000100013Q0020CB00010001000100060F0001005100013Q0004D03Q005100012Q003A000100024Q00B3000200013Q00202Q00020002000100102Q0001000100024Q000100026Q000200013Q00202Q00020002000200102Q0001000200022Q003A000100024Q00B3000200013Q00202Q00020002000300102Q0001000300024Q000100026Q000200013Q00202Q00020002000400102Q0001000400022Q003A000100024Q00B3000200013Q00202Q00020002000500102Q0001000500024Q000100026Q000200013Q00202Q00020002000600102Q0001000600022Q00BA3Q00013Q00013Q000D3Q0003073Q00416D6269656E7403063Q00436F6C6F723303073Q0066726F6D524742025Q00E06F40030E3Q004F7574642Q6F72416D6269656E74030A3Q004272696768746E652Q73027Q004003093Q00436C6F636B54696D65026Q002C4003063Q00466F67456E64025Q006AF840030D3Q00476C6F62616C536861646F7773012Q00194Q007E016Q00122Q000100023Q00202Q00010001000300122Q000200043Q00122Q000300043Q00122Q000400046Q00010004000200104Q000100019Q0000122Q000100023Q00202Q00010001000300122Q000200043Q00122Q000300043Q00122Q000400046Q00010004000200104Q000500019Q0000304Q000600079Q0000304Q000800099Q0000304Q000A000B9Q0000304Q000C000D6Q00017Q00193Q0003053Q007063612Q6C03063Q00697061697273030B3Q004765744368696C6472656E2Q033Q00497341030A3Q00506F7374452Q6665637403073Q00456E61626C6564010003093Q00776F726B7370616365030E3Q0047657444657363656E64616E747303083Q004261736550617274030E3Q00497344657363656E64616E744F6603093Q004368617261637465722Q033Q004D617403083Q004D6174657269616C03063Q00536861646F77030A3Q0043617374536861646F7703043Q00456E756D030D3Q00536D2Q6F7468506C617374696303053Q00446563616C03073Q00546578747572652Q033Q00547261030C3Q005472616E73706172656E6379026Q00F03F03053Q00706169727303063Q00506172656E74016E3Q00060F3Q004700013Q0004D03Q004700010012572Q0100013Q00022201026Q001B2Q010002000100122Q000100026Q00025Q00202Q0002000200034Q000200036Q00013Q000300044Q0014000100204401060005000400128E010800054Q009000060008000200060F0006001400013Q0004D03Q001400012Q003A000600013Q0020CB0007000500062Q00E600060005000700304C0005000600070006482Q01000B000100020004D03Q000B00010012572Q0100023Q001246000200083Q00202Q0002000200094Q000200036Q00013Q000300044Q0044000100204401060005000400128E0108000A4Q009000060008000200060F0006003400013Q0004D03Q0034000100204401060005000B2Q003A000800023Q0020CB00080008000C2Q009000060008000200065801060034000100010004D03Q003400012Q003A000600034Q00C400073Q000200202Q00080005000E00102Q0007000D000800202Q00080005001000102Q0007000F00084Q00060005000700122Q000600113Q00202Q00060006000E00202Q00060006001200102Q0005000E000600304C0005001000070004D03Q0044000100204401060005000400128E010800134Q00900006000800020006580106003E000100010004D03Q003E000100204401060005000400128E010800144Q009000060008000200060F0006004400013Q0004D03Q004400012Q003A000600034Q000C01073Q000100202Q00080005001600102Q0007001500084Q00060005000700302Q0005001600170006482Q01001C000100020004D03Q001C00010004D03Q006D00010012572Q0100013Q000222010200014Q000A00010002000100122Q000100186Q000200036Q00010002000300044Q0069000100060F0004006900013Q0004D03Q006900010020CB00060004001900060F0006006900013Q0004D03Q0069000100204401060004000400128E0108000A4Q009000060008000200060F0006005D00013Q0004D03Q005D00010020CB00060005000D0020CB00070005000F00107A00040010000700107A0004000E00060004D03Q0069000100204401060004000400128E010800134Q009000060008000200065801060067000100010004D03Q0067000100204401060004000400128E010800144Q009000060008000200060F0006006900013Q0004D03Q006900010020CB00060005001500107A0004001600060006482Q01004E000100020004D03Q004E00012Q008100016Q00A62Q0100034Q00BA3Q00013Q00023Q00053Q0003083Q0073652Q74696E677303093Q0052656E646572696E67030C3Q005175616C6974794C6576656C03043Q00456E756D03073Q004C6576656C303100083Q0012873Q00018Q0001000200206Q000200122Q000100043Q00202Q00010001000300202Q00010001000500104Q000300016Q00017Q00053Q0003083Q0073652Q74696E677303093Q0052656E646572696E67030C3Q005175616C6974794C6576656C03043Q00456E756D03093Q004175746F6D6174696300083Q0012873Q00018Q0001000200206Q000200122Q000100043Q00202Q00010001000300202Q00010001000500104Q000300016Q00017Q00093Q00030C3Q00736574636C6970626F617264031D3Q00682Q7470733A2Q2F646973636F72642E2Q672F337A3632664D3677474503063Q004E6F7469667903053Q005469746C65030B3Q005665726F7573205761766503073Q00436F6E74656E7403143Q00446973636F7264206C696E6B20636F706965642103083Q004475726174696F6E026Q001440000D4Q00AB9Q003Q0001000100124Q00013Q00122Q000100028Q000200016Q00013Q00206Q00034Q00023Q000300302Q00020004000500302Q00020006000700302Q0002000800096Q000200016Q00017Q00013Q0003053Q007063612Q6C00114Q003A8Q002B3Q00010001001257012Q00013Q00067900013Q0001000B2Q003A3Q00014Q003A3Q00024Q003A3Q00034Q003A3Q00044Q003A3Q00054Q003A3Q00064Q003A3Q00074Q003A3Q00084Q003A3Q00094Q003A3Q000A4Q003A3Q000B4Q009A3Q000200012Q00BA3Q00013Q00013Q000B3Q0003083Q0053657456616C7565030E3Q00456E68616E636564546F2Q676C6503083Q004F726967696E616C03073Q0044657374726F7903063Q004E6F7469667903053Q005469746C65030B3Q005665726F7573205761766503073Q00436F6E74656E74031E3Q00412Q6C2073797374656D732073746F2Q70656420616E642072657365742103083Q004475726174696F6E026Q00144000464Q003A7Q00060F3Q000700013Q0004D03Q000700012Q003A7Q002044014Q00012Q007100026Q00A2012Q000200012Q003A3Q00013Q00060F3Q000E00013Q0004D03Q000E00012Q003A3Q00013Q002044014Q00012Q007100026Q00A2012Q000200012Q003A3Q00023Q00060F3Q001500013Q0004D03Q001500012Q003A3Q00023Q002044014Q00012Q007100026Q00A2012Q000200012Q003A3Q00033Q00060F3Q001C00013Q0004D03Q001C00012Q003A3Q00033Q002044014Q00012Q007100026Q00A2012Q000200012Q003A3Q00043Q00060F3Q002300013Q0004D03Q002300012Q003A3Q00043Q002044014Q00012Q007100026Q00A2012Q000200012Q003A3Q00053Q00209D5Q00014Q00029Q000002000100124Q00023Q00206Q00014Q00029Q00000200016Q00063Q00206Q00014Q00026Q00A2012Q000200012Q003A3Q00073Q002044014Q00012Q007100026Q00A2012Q000200012Q003A3Q00083Q00128E2Q0100034Q009A3Q000200012Q003A3Q00093Q00060F3Q003E00013Q0004D03Q003E00012Q003A3Q00093Q002044014Q00042Q009A3Q000200012Q009D017Q00A6012Q00094Q003A3Q000A3Q002061014Q00054Q00023Q000300302Q00020006000700302Q00020008000900302Q0002000A000B6Q000200012Q00BA3Q00017Q00013Q0003043Q00506C617901084Q00A6017Q003A00015Q00060F0001000700013Q0004D03Q000700012Q003A000100013Q0020442Q01000100012Q009A0001000200012Q00BA3Q00017Q000B3Q0003063Q004E6F7469667903053Q005469746C65030B3Q005665726F7573205761766503073Q00436F6E74656E74031C3Q004C6F6164696E672054726F2Q6C2043612Q72792045766164653Q2E03083Q004475726174696F6E026Q000840030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403743Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F61646977706961736F702Q647761373866617364376173366431763661343877613776736164762F54726F2Q6C2D43612Q72792D45766164652F726566732F68656164732F6D61696E2F6D61696E2E6C756100114Q00749Q003Q000100016Q00013Q00206Q00014Q00023Q000300302Q00020002000300302Q00020004000500302Q0002000600076Q0002000100124Q00083Q00122Q000100093Q00202Q00010001000A00122Q0003000B6Q000100039Q0000026Q000100016Q00017Q00173Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C64030E3Q005469636B6574536166655A6F6E6503083Q00496E7374616E63652Q033Q006E657703043Q005061727403043Q004E616D6503043Q0053697A6503073Q00566563746F7233026Q004940027Q004003083Q00506F736974696F6E030B3Q00536166655A6F6E65506F73028Q00026Q00104003083Q00416E63686F726564030A3Q0043616E436F2Q6C6964652Q01030C3Q005472616E73706172656E637903083Q004D6174657269616C026Q00E03F03043Q00456E756D03043Q004E656F6E00283Q0012B93Q00013Q00206Q000200122Q000200038Q0002000200064Q000700013Q0004D03Q000700012Q00BA3Q00013Q001257012Q00043Q0020D65Q000500122Q000100063Q00122Q000200018Q0002000200304Q0007000300122Q000100093Q00202Q00010001000500122Q0002000A3Q00122Q0003000B3Q00122Q0004000A6Q00010004000200104Q000800014Q00015Q00202Q00010001000D00122Q000200093Q00202Q00020002000500122Q0003000E3Q00122Q0004000F3Q00122Q0005000E6Q0002000500024Q00010001000200104Q000C00014Q000100013Q00304Q0011001200104Q0010000100122Q000100153Q00122Q000200163Q00202Q00020002001400202Q00020002001700104Q0014000200104Q001300016Q00017Q000F3Q0003083Q00496E7374616E63652Q033Q006E657703093Q00486967686C6967687403093Q0046692Q6C436F6C6F7203063Q00436F6C6F723303073Q0066726F6D524742025Q00E06F40028Q0003073Q0044726177696E6703043Q004C696E6503073Q0056697369626C6503053Q00436F6C6F7203093Q00546869636B6E652Q73026Q00F03F03043Q005061727401254Q003A00016Q00D1000100013Q00060F0001000500013Q0004D03Q000500012Q00BA3Q00013Q0012572Q0100013Q0020B800010001000200122Q000200036Q00038Q00010003000200122Q000200053Q00202Q00020002000600122Q000300073Q00122Q000400083Q00122Q000500086Q00020005000200102Q00010004000200122Q000200093Q00202Q00020002000200122Q0003000A6Q0002000200024Q00035Q00122Q000400053Q00202Q00040004000600122Q000500073Q00122Q000600083Q00122Q000700086Q00040007000200302Q0002000D000E00102Q0002000C000400102Q0002000B00034Q00038Q00043Q000200102Q0004000A000200102Q0004000F6Q00033Q00046Q00017Q00153Q002Q033Q0045535003073Q00566563746F72322Q033Q006E657703093Q00776F726B7370616365030D3Q0043752Q72656E7443616D657261030C3Q0056696577706F727453697A6503013Q0058027Q004003013Q005903053Q00706169727303043Q005061727403063Q00506172656E7403043Q004C696E6503063Q0052656D6F76650003143Q00576F726C64546F56696577706F7274506F696E7403083Q00506F736974696F6E03073Q0056697369626C6503043Q0046726F6D03023Q00546F012Q00404Q003A7Q0020CB5Q000100060F3Q003F00013Q0004D03Q003F0001001257012Q00023Q002035014Q000300122Q000100043Q00202Q00010001000500202Q00010001000600202Q00010001000700202Q00010001000800122Q000200043Q00202Q00020002000500202Q00020002000600202Q00020002000900202Q0002000200086Q0002000200122Q0001000A6Q000200016Q00010002000300044Q003D00010020CB00060005000B00060F0006001C00013Q0004D03Q001C00010020CB00060005000B0020CB00060006000C00065801060025000100010004D03Q002500010020CB00060005000D00060F0006002200013Q0004D03Q002200010020CB00060005000D00204401060006000E2Q009A0006000200012Q003A000600013Q00205A01060004000F0004D03Q003D0001001257010600043Q00201500060006000500202Q00060006001000202Q00080005000B00202Q0008000800114Q00060008000700062Q0007003B00013Q0004D03Q003B00010020CB00080005000D00203F00090005000D00202Q000A0005000D4Q000B00016Q000C5Q00122Q000D00023Q00202Q000D000D000300202Q000E0006000700202Q000F000600094Q000D000F000200102Q000A0014000D00102Q00090013000C00102Q00080012000B00044Q003D00010020CB00080005000D00304C0008001200150006482Q010015000100020004D03Q001500012Q00BA3Q00017Q001A3Q0003043Q007461736B03043Q0077616974029A5Q99A93F03083Q004175746F4661726D03043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q00426173655061727403053Q007461626C6503063Q00696E73657274028Q0003083Q004973417442617365010003063Q00434672616D65026Q00F03F2Q033Q006E6577030B3Q00536166655A6F6E65506F7303073Q00566563746F7233026Q0008402Q01004A3Q001257012Q00013Q0020CB5Q000200128E2Q0100034Q001F012Q0002000200060F3Q004900013Q0004D03Q004900012Q003A7Q0020CB5Q000400060F5Q00013Q0004D05Q0001001257012Q00053Q0020CB5Q00060020CB5Q00070020CB5Q000800060F3Q001700013Q0004D03Q00170001001257012Q00053Q0020F05Q000600206Q000700206Q000800206Q000900122Q0002000A8Q0002000200060F5Q00013Q0004D05Q00012Q008100015Q0012790102000B6Q000300013Q00202Q00030003000C4Q000300046Q00023Q000400044Q002A000100204401070006000D00128E0109000E4Q009000070009000200060F0007002A00013Q0004D03Q002A00010012570107000F3Q0020CB0007000700102Q0082010800014Q0082010900064Q00A201070009000100064801020020000100020004D03Q002000012Q005B000200013Q000E2C00110035000100020004D03Q003500012Q003A00025Q00300500020012001300202Q00020001001500202Q00020002001400104Q0014000200046Q00012Q003A00025Q0020CB00020002001200065801023Q000100010004D05Q0001001257010200143Q00206E0102000200164Q00035Q00202Q00030003001700122Q000400183Q00202Q00040004001600122Q000500113Q00122Q000600193Q00122Q000700116Q0004000700024Q0003000300044Q00020002000200104Q001400024Q00025Q00302Q00020012001A00046Q00012Q00BA3Q00017Q00013Q0003083Q004175746F4661726D01094Q00182Q018Q0001000100014Q000100013Q00102Q000100013Q00064Q000800013Q0004D03Q000800012Q003A000100024Q002B0001000100012Q00BA3Q00017Q00093Q002Q033Q0045535003053Q00706169727303043Q004C696E6503073Q0056697369626C65010003063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q00426173655061727401204Q00ED00018Q0001000100014Q000100013Q00102Q000100013Q00064Q000F000100010004D03Q000F00010012572Q0100024Q003A000200024Q00FC0001000200030004D03Q000C00010020CB00060005000300304C0006000400050006482Q01000A000100020004D03Q000A00010004D03Q001F00010012572Q0100064Q0001000200033Q00202Q0002000200074Q000200036Q00013Q000300044Q001D000100204401060005000800128E010800094Q009000060008000200060F0006001D00013Q0004D03Q001D00012Q003A000600044Q0082010700054Q009A0006000200010006482Q010015000100020004D03Q001500012Q00BA3Q00017Q001A3Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403093Q00776F726B737061636503163Q0046696E6446697273744368696C645768696368497341030D3Q00537061776E4C6F636174696F6E03083Q0056656C6F6369747903073Q00566563746F72332Q033Q006E6577028Q0003073Q005069766F74546F03063Q00434672616D65026Q00144003043Q007461736B03043Q0077616974029A5Q99B93F03063Q004E6F7469667903053Q005469746C6503083Q0054656C65706F727403073Q00436F6E74656E74031B3Q0054656C65706F7274656420746F20537061776E20736166656C792103083Q004475726174696F6E027Q004003053Q00452Q726F7203233Q004E6F20537061776E4C6F636174696F6E20666F756E6420696E2074686973206D617021026Q00084000454Q00CF9Q003Q000100016Q00013Q00206Q000100064Q004400013Q0004D03Q004400010020442Q013Q000200128E010300034Q009000010003000200060F0001004400013Q0004D03Q004400010012572Q0100043Q0020662Q010001000500122Q000300066Q000400016Q00010004000200062Q0001003D00013Q0004D03Q003D00010020CB00023Q000300127C010300083Q00202Q00030003000900122Q0004000A3Q00122Q0005000A3Q00122Q0006000A6Q00030006000200102Q00020007000300202Q00023Q000B00202Q00040001000C00122Q000500083Q00202Q00050005000900122Q0006000A3Q00122Q0007000D3Q00122Q0008000A6Q0005000800024Q0004000400054Q00020004000100122Q0002000E3Q00202Q00020002000F00122Q000300106Q00020002000100202Q00023Q000200122Q000400036Q00020004000200062Q0002003500013Q0004D03Q003500010020CB00023Q0003001276000300083Q00202Q00030003000900122Q0004000A3Q00122Q0005000A3Q00122Q0006000A6Q00030006000200102Q0002000700032Q003A000200023Q0020DC0002000200114Q00043Q000300302Q00040012001300302Q00040014001500302Q0004001600174Q00020004000100044Q004400012Q003A000200023Q0020610102000200114Q00043Q000300302Q00040012001800302Q00040014001900302Q00040016001A4Q0002000400012Q00BA3Q00017Q001F3Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403063Q00434672616D652Q033Q006E6577028Q00025Q00408F4003093Q0057616C6B53702Q656403093Q004A756D70506F77657203083Q00496E7374616E636503043Q005061727403093Q00776F726B737061636503043Q004E616D65030E3Q00536166657479506C6174666F726D03043Q0053697A6503073Q00566563746F7233026Q003440026Q00F03F026Q000CC003083Q00416E63686F7265642Q01030C3Q005472616E73706172656E6379026Q00E03F030A3Q00446973636F2Q6E65637403093Q0048656172746265617403073Q00436F2Q6E65637403073Q0044657374726F79026Q003040026Q004940017B4Q003A00015Q0020CB00010001000100069E00020007000100010004D03Q0007000100204401020001000200128E010400034Q009000020004000200069E0003000C000100010004D03Q000C000100204401030001000400128E010500054Q00900003000500022Q00A6012Q00014Q003A000400013Q00060F0004005100013Q0004D03Q0051000100060F0002007A00013Q0004D03Q007A000100060F0003007A00013Q0004D03Q007A00010020CB0004000200062Q003C000400026Q000400023Q00122Q000500063Q00202Q00050005000700122Q000600083Q00122Q000700093Q00122Q000800086Q0005000800024Q0004000400054Q000400036Q000400033Q00102Q00020006000400302Q0003000A000800302Q0003000B000800122Q0004000C3Q00202Q00040004000700122Q0005000D3Q00122Q0006000E6Q0004000600024Q000400046Q000400043Q00302Q0004000F00104Q000400043Q00122Q000500123Q00202Q00050005000700122Q000600133Q00122Q000700143Q00122Q000800136Q00050008000200102Q0004001100054Q000400046Q000500033Q00122Q000600063Q00202Q00060006000700122Q000700083Q00122Q000800153Q00122Q000900086Q0006000900024Q00050005000600102Q0004000600054Q000400043Q00302Q0004001600174Q000400043Q00302Q0004001800194Q000400053Q00062Q0004004700013Q0004D03Q004700012Q003A000400053Q00204401040004001A2Q009A0004000200012Q003A000400063Q0020CB00040004001B00204401040004001C00067900063Q000100032Q003A8Q003A3Q00014Q003A3Q00034Q00900004000600022Q00A6010400053Q0004D03Q007A00012Q007100046Q00A6010400014Q003A000400053Q00060F0004005B00013Q0004D03Q005B00012Q003A000400053Q00204401040004001A2Q009A0004000200012Q009D010400044Q00A6010400054Q003A000400043Q00060F0004006300013Q0004D03Q006300012Q003A000400043Q00204401040004001D2Q009A0004000200012Q009D010400044Q00A6010400044Q003A00045Q0020CB00040004000100069E0005006A000100040004D03Q006A000100204401050004000200128E010700034Q009000050007000200069E0006006F000100040004D03Q006F000100204401060004000400128E010800054Q00900006000800022Q003A000700023Q00060F0007007600013Q0004D03Q0076000100060F0005007600013Q0004D03Q007600012Q003A000700023Q00107A00050006000700060F0006007A00013Q0004D03Q007A000100304C0006000A001E00304C0006000B001F2Q00BA3Q00013Q00013Q000C3Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403083Q00506F736974696F6E03093Q004D61676E6974756465026Q00144003063Q00434672616D6503093Q0057616C6B53702Q6564028Q0003093Q004A756D70506F77657200224Q003A7Q0020CB5Q000100069E0001000700013Q0004D03Q000700010020442Q013Q000200128E010300034Q009000010003000200069E0002000C00013Q0004D03Q000C000100204401023Q000400128E010400054Q00900002000400022Q003A000300013Q00060F0003002100013Q0004D03Q0021000100060F0001002100013Q0004D03Q002100010020CB0003000100062Q0033000400023Q00202Q0004000400064Q00030003000400202Q000300030007000E2Q0008001A000100030004D03Q001A00012Q003A000300023Q00107A00010009000300060F0002002100013Q0004D03Q002100010020CB00030002000A00266A010300210001000B0004D03Q0021000100304C0002000A000B00304C0002000C000B2Q00BA3Q00017Q00143Q00030D3Q0052617963617374506172616D732Q033Q006E6577030A3Q0046696C7465725479706503043Q00456E756D03113Q005261796361737446696C7465725479706503073Q004578636C756465031A3Q0046696C74657244657363656E64616E7473496E7374616E63657303093Q0043686172616374657203093Q00776F726B7370616365030E3Q0046696E6446697273744368696C6403083Q004E657874626F747303073Q005261796361737403073Q00566563746F7233028Q00026Q001440026Q0034C003083Q00496E7374616E6365030A3Q0043616E436F2Q6C69646503083Q00506F736974696F6E026Q00084001363Q0012C8000100013Q00202Q0001000100024Q00010001000200122Q000200043Q00202Q00020002000500202Q00020002000600102Q0001000300024Q000200016Q00035Q00202Q00030003000800122Q000400093Q00202Q00040004000A00122Q0006000B6Q000400066Q00023Q000100107A000100070002001228000200093Q00202Q00020002000C00122Q0004000D3Q00202Q00040004000200122Q0005000E3Q00122Q0006000F3Q00122Q0007000E6Q0004000700024Q00043Q000400122Q0005000D3Q00202Q00050005000200122Q0006000E3Q00122Q000700103Q00122Q0008000E6Q0005000800024Q000600016Q00020006000200062Q0002003300013Q0004D03Q003300010020CB00030002001100060F0003003300013Q0004D03Q003300010020CB0003000200110020CB00030003001200060F0003003300013Q0004D03Q003300010020CB0003000200130012EF0004000D3Q00202Q00040004000200122Q0005000E3Q00122Q000600143Q00122Q0007000E6Q0004000700024Q0003000300044Q000300024Q009D010300034Q00DD000300024Q00BA3Q00017Q000E3Q0003043Q0067616D65030A3Q0047657453657276696365030A3Q0052756E5365727669636503093Q0048656172746265617403073Q00436F2Q6E65637403063Q004E6F7469667903053Q005469746C6503083Q00537572766976616C03073Q00436F6E74656E7403143Q00536166652045736361706520456E61626C65642103083Q004475726174696F6E027Q0040030A3Q00446973636F2Q6E65637403153Q0053616665204573636170652044697361626C656421012A4Q00A02Q018Q0001000100016Q00016Q000100013Q00062Q0001001A00013Q0004D03Q001A00010012572Q0100013Q00209F00010001000200122Q000300036Q00010003000200202Q00010001000400202Q00010001000500067900033Q000100032Q003A3Q00034Q003A3Q00044Q003A3Q00054Q00900001000300022Q00D4000100026Q000100063Q00202Q0001000100064Q00033Q000300302Q00030007000800302Q00030009000A00302Q0003000B000C4Q0001000300010004D03Q002900012Q003A000100023Q00060F0001002200013Q0004D03Q002200012Q003A000100023Q0020442Q010001000D2Q009A0001000200012Q009D2Q0100014Q00A62Q0100024Q003A000100063Q0020612Q01000100064Q00033Q000300302Q00030007000800302Q00030009000E00302Q0003000B000C4Q0001000300012Q00BA3Q00013Q00013Q00183Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q00506F736974696F6E03063Q00434672616D65030D3Q004F7665726C6170506172616D732Q033Q006E6577030A3Q0046696C7465725479706503043Q00456E756D03113Q005261796361737446696C7465725479706503073Q004578636C756465031A3Q0046696C74657244657363656E64616E7473496E7374616E63657303093Q00776F726B737061636503153Q0047657450617274426F756E6473496E526164697573026Q00344003053Q00706169727303183Q0046696E644669727374416E636573746F724F66436C612Q7303053Q004D6F64656C03043Q0067616D6503073Q00506C617965727303163Q00476574506C6179657246726F6D436861726163746572030B3Q005072696D6172795061727403043Q00556E6974026Q00544000574Q003A7Q0020CB5Q000100069E0001000700013Q0004D03Q000700010020442Q013Q000200128E010300034Q00900001000300020006582Q01000A000100010004D03Q000A00012Q00BA3Q00014Q003A000200013Q0020CB0003000100042Q001F01020002000200060F0002001100013Q0004D03Q001100010020CB0003000100052Q00A6010300023Q001257010300063Q0020990103000300074Q00030001000200122Q000400093Q00202Q00040004000A00202Q00040004000B00102Q0003000800044Q000400016Q00058Q00040001000100107A0003000C000400120A0104000D3Q00202Q00040004000E00202Q00060001000400122Q0007000F6Q000800036Q00040008000200122Q000500106Q000600046Q00050002000700044Q00540001002044010A0009001100128E010C00124Q0090000A000C000200060F000A005400013Q0004D03Q005400010006C5000A005400013Q0004D03Q00540001001257010B00133Q002090010B000B001400202Q000B000B00154Q000D000A6Q000B000D000200062Q000B0054000100010004D03Q00540001002044010B000A000200128E010D00034Q0090000B000D0002000658010B003A000100010004D03Q003A00010020CB000B000A001600060F000B005400013Q0004D03Q005400010020CB000C0001000400201C000D000B00044Q000C000C000D00202Q000C000C001700202Q000D0001000400202Q000E000C00184Q000D000D000E4Q000E00016Q000F000D6Q000E0002000200062Q000E004E00013Q0004D03Q004E0001001257010F00053Q00207D000F000F00074Q0010000E6Q000F0002000200102Q00010005000F00044Q005600012Q003A000F00023Q00060F000F005600013Q0004D03Q005600012Q003A000F00023Q00107A00010005000F0004D03Q0056000100064801050026000100020004D03Q002600012Q00BA3Q00017Q00063Q0003063Q00506172656E7403083Q00496E7374616E63652Q033Q006E657703053Q00536F756E6403043Q004E616D6503113Q00437573746F6D4D75736963506C6179657200144Q003A7Q00060F3Q000700013Q0004D03Q000700012Q003A7Q0020CB5Q0001000658012Q0011000100010004D03Q00110001001257012Q00023Q002028014Q000300122Q000100048Q000200029Q009Q0000304Q000500069Q004Q000100013Q00104Q000100012Q003A8Q00DD3Q00024Q00BA3Q00019Q002Q0001024Q00A6017Q00BA3Q00017Q000C3Q00034Q0003063Q004E6F7469667903053Q005469746C6503053Q004D7573696303073Q00436F6E74656E7403143Q00506C65617365205479706520536F756E6420494403083Q004475726174696F6E027Q004003073Q00536F756E644964030D3Q00726278612Q73657469643A2Q2F03043Q00506C6179030F3Q00506C617920536F756E642049443A20001E4Q003A7Q002654012Q000B000100010004D03Q000B00012Q003A3Q00013Q002061014Q00024Q00023Q000300302Q00020003000400302Q00020005000600302Q0002000700086Q000200012Q00BA3Q00014Q003A3Q00024Q00C33Q0001000200122Q0001000A6Q00028Q00010001000200104Q0009000100202Q00013Q000B4Q0001000200014Q000100013Q00202Q0001000100024Q00033Q000300302Q00030003000400122Q0004000C6Q00058Q00040004000500102Q00030005000400302Q0003000700084Q0001000300016Q00017Q00083Q0003043Q0053746F7003063Q004E6F7469667903053Q005469746C6503053Q004D7573696303073Q00436F6E74656E74030A3Q0053746F7020536F756E6403083Q004475726174696F6E027Q0040000E4Q003A7Q00060F3Q000D00013Q0004D03Q000D00012Q003A7Q00201A014Q00016Q000200016Q00013Q00206Q00024Q00023Q000300302Q00020003000400302Q00020005000600302Q0002000700086Q000200012Q00BA3Q00017Q000C3Q0003063Q004C2Q6F70656403083Q005365745469746C65030F3Q0053746F70204C2Q6F7020536F756E6403063Q004E6F7469667903053Q005469746C6503053Q004D7573696303073Q00436F6E74656E7403133Q004C2Q6F7020536F756E64207C20456E61626C6503083Q004475726174696F6E027Q0040030A3Q004C2Q6F7020536F756E6403143Q004C2Q6F7020536F756E64207C2044697361626C6500224Q00D39Q009Q009Q003Q00018Q000100024Q00015Q00104Q000100014Q00015Q00062Q0001001600013Q0004D03Q001600012Q003A000100023Q00208900010001000200122Q000300036Q0001000300014Q000100033Q00202Q0001000100044Q00033Q000300302Q00030005000600302Q00030007000800302Q00030009000A4Q0001000300010004D03Q002100012Q003A000100023Q00208900010001000200122Q0003000B6Q0001000300014Q000100033Q00202Q0001000100044Q00033Q000300302Q00030005000600302Q00030007000C00302Q00030009000A4Q0001000300012Q00BA3Q00017Q00023Q0003083Q00746F6E756D62657203063Q00566F6C756D6501093Q0012572Q0100014Q008201026Q001F2Q010002000200060F0001000800013Q0004D03Q000800012Q003A00026Q009F01020001000200107A0002000200012Q00BA3Q00017Q00043Q0003083Q00746F6E756D626572023Q0080B5F8E43E025Q0088C340030D3Q00506C61796261636B53702Q6564010F3Q0012572Q0100014Q008201026Q001F2Q010002000200060F0001000E00013Q0004D03Q000E00010026062Q010008000100020004D03Q0008000100128E2Q0100023Q000E2C0003000B000100010004D03Q000B000100128E2Q0100034Q003A00026Q009F01020001000200107A0002000400012Q00BA3Q00017Q000A3Q0003073Q00536F756E644964030D3Q00726278612Q73657469643A2Q2F03043Q00506C617903063Q004E6F7469667903053Q005469746C65030C3Q004D7573696320506C6179657203073Q00436F6E74656E74030D3Q004E6F7720506C6179696E673A2003083Q004475726174696F6E026Q00084001184Q003A00016Q00D1000100013Q00060F0001001700013Q0004D03Q001700012Q00A62Q0100014Q0047010200026Q00020001000200122Q000300026Q000400016Q00030003000400102Q00020001000300202Q0003000200034Q0003000200014Q000300033Q00202Q0003000300044Q00053Q000300302Q00050005000600122Q000600086Q00078Q00060006000700102Q00050007000600302Q00050009000A4Q0003000500012Q00BA3Q00019Q002Q0001024Q00A6017Q00BA3Q00017Q002E3Q00034Q00026Q00084003063Q004E6F7469667903053Q005469746C6503063Q0053797374656D03073Q00436F6E74656E7403223Q00506C656173652074797065206174206C65617374203320636861726163746572732E03083Q004475726174696F6E03073Q00636F6E74656E74031F3Q00F09F93A2202Q2A4E657720462Q65646261636B205265636569766564212Q2A03063Q00656D6265647303053Q007469746C65033E3Q00F09F93A920E0B882E0B989E0B8ADE0B884E0B8A7E0B8B2E0B8A1E0B888E0B8B2E0B881E0B89CE0B8B9E0B989E0B983E0B88AE0B989E0B887E0B8B2E0B899030B3Q006465736372697074696F6E03053Q00636F6C6F7203083Q00746F6E756D626572025Q00E06F4103063Q006669656C647303043Q006E616D6503103Q00F09F91A420506C61796572204E616D6503053Q0076616C756503043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203043Q004E616D6503063Q00696E6C696E652Q01030B3Q00F09F86942055736572494403083Q00746F737472696E6703063Q00557365724964030C3Q00F09F8EAE2047616D6520494403073Q00506C616365496403063Q00662Q6F74657203043Q007465787403193Q0053656E742066726F6D20466C75656E742047554920E280A22003023Q006F7303043Q006461746503023Q00255803053Q007063612Q6C03073Q0053752Q63652Q7303163Q00462Q65646261636B2053752Q63652Q732053656E7421026Q00144003053Q00452Q726F72030F3Q00462Q65646261636B204661696C656403043Q007761726E030F3Q00576562682Q6F6B20452Q726F723A2000634Q003A7Q00266A012Q0007000100010004D03Q000700012Q003A8Q005B7Q002606012Q000F000100020004D03Q000F00012Q003A3Q00013Q002061014Q00034Q00023Q000300302Q00020004000500302Q00020006000700302Q0002000800026Q000200012Q00BA3Q00014Q00815Q000200301E3Q0009000A4Q000100016Q00023Q000500302Q0002000C000D4Q00035Q00102Q0002000E000300122Q000300103Q00122Q000400116Q00030002000200102Q0002000F00034Q000300036Q00043Q000300302Q00040013001400122Q000500163Q00202Q00050005001700202Q00050005001800202Q00050005001900102Q00040015000500302Q0004001A001B4Q00053Q000300302Q00050013001C00122Q0006001D3Q00122Q000700163Q00202Q00070007001700202Q00070007001800202Q00070007001E4Q00060002000200102Q00050015000600302Q0005001A001B4Q00063Q000300302Q00060013001F00122Q0007001D3Q00122Q000800163Q00202Q0008000800204Q00070002000200102Q00060015000700302Q0006001A001B4Q00030003000100107A0002001200032Q002Q01033Q000100122Q000400233Q00122Q000500243Q00202Q00050005002500122Q000600266Q0005000200024Q00040004000500102Q00030022000400102Q0002002100034Q00010001000100107A3Q000B00010012572Q0100273Q00067900023Q000100032Q003A3Q00024Q0082017Q003A3Q00034Q00FC00010002000200060F0001005400013Q0004D03Q005400012Q003A000300013Q0020610103000300034Q00053Q000300302Q00050004002800302Q00050006002900302Q00050008002A4Q00030005000100128E010300014Q00A601035Q0004D03Q006200012Q003A000300013Q0020610103000300034Q00053Q000300302Q00050004002B00302Q00050006002C00302Q00050008002A4Q0003000500010012AD0003002D3Q00122Q0004002E3Q00122Q0005001D6Q000600026Q0005000200024Q0004000400054Q0003000200012Q00BA3Q00013Q00013Q00093Q00030A3Q004A534F4E456E636F646503073Q00726571756573742Q033Q0055726C03063Q004D6574686F6403043Q00504F535403073Q0048656164657273030C3Q00436F6E74656E742D5479706503103Q00612Q706C69636174696F6E2F6A736F6E03043Q00426F6479000F4Q00607Q00206Q00014Q000200018Q0002000200122Q000100026Q00023Q00044Q000300023Q00102Q00020003000300302Q0002000400054Q00033Q000100302Q00030007000800102Q00020006000300102Q000200096Q0001000200016Q00019Q003Q00094Q00DE9Q009Q009Q003Q00019Q008Q00029Q008Q00038Q00017Q000E3Q0003063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q00426173655061727403053Q007461626C6503063Q00696E73657274030B3Q005370656369616C4D65736803053Q00446563616C03073Q005465787475726503153Q0046696E6446697273744368696C644F66436C612Q73030A3Q00426F6479436F6C6F727303083Q00496E7374616E63652Q033Q006E657703063Q00506172656E7401404Q003A00016Q002B000100010001000658012Q0005000100010004D03Q000500012Q00BA3Q00013Q0012572Q0100013Q00204401023Q00022Q002D000200034Q00132Q013Q00030004D03Q002F000100204401060005000300128E010800044Q009000060008000200060F0006001500013Q0004D03Q00150001001257010600053Q0020290106000600064Q000700016Q000800056Q00060008000100044Q002F000100204401060005000300128E010800074Q009000060008000200060F0006002000013Q0004D03Q00200001001257010600053Q0020290106000600064Q000700026Q000800056Q00060008000100044Q002F000100204401060005000300128E010800084Q00900006000800020006580106002A000100010004D03Q002A000100204401060005000300128E010800094Q009000060008000200060F0006002F00013Q0004D03Q002F0001001257010600053Q0020CB0006000600062Q003A000700034Q0082010800054Q00A20106000800010006482Q01000A000100020004D03Q000A00010020442Q013Q000A0012070003000B6Q0001000300024Q000100046Q000100043Q00062Q0001003F000100010004D03Q003F00010012572Q01000C3Q00206F2Q010001000D00122Q0002000B6Q0001000200024Q000100046Q000100043Q00102Q0001000E4Q00BA3Q00017Q00193Q0003093Q0043686172616374657203063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q00426173655061727403053Q00436F6C6F72030B3Q005370656369616C4D657368030B3Q00566572746578436F6C6F7203053Q00446563616C03073Q005465787475726503063Q00436F6C6F723303153Q0046696E6446697273744368696C644F66436C612Q73030A3Q00426F6479436F6C6F7273030A3Q0048656164436F6C6F723303043Q0048656164030B3Q00546F72736F436F6C6F723303053Q00546F72736F030D3Q004C65667441726D436F6C6F723303073Q004C65667441726D030E3Q00526967687441726D436F6C6F723303083Q00526967687441726D030D3Q004C6566744C6567436F6C6F723303073Q004C6566744C6567030E3Q0052696768744C6567436F6C6F723303083Q0052696768744C656700504Q003A7Q0020CB5Q000100060F3Q004D00013Q0004D03Q004D00010012572Q0100023Q00204401023Q00032Q002D000200034Q00132Q013Q00030004D03Q0034000100204401060005000400128E010800054Q009000060008000200060F0006001600013Q0004D03Q001600012Q003A000600014Q00D100060006000500060F0006001600013Q0004D03Q001600012Q003A000600014Q00D100060006000500107A0005000600060004D03Q0034000100204401060005000400128E010800074Q009000060008000200060F0006002300013Q0004D03Q002300012Q003A000600014Q00D100060006000500060F0006002300013Q0004D03Q002300012Q003A000600014Q00D100060006000500107A0005000800060004D03Q0034000100204401060005000400128E010800094Q00900006000800020006580106002D000100010004D03Q002D000100204401060005000400128E0108000A4Q009000060008000200060F0006003400013Q0004D03Q003400012Q003A000600014Q00D100060006000500060F0006003400013Q0004D03Q003400012Q003A000600014Q00D100060006000500107A0005000B00060006482Q010009000100020004D03Q000900010020442Q013Q000C00128E0103000D4Q009000010003000200060F0001004D00013Q0004D03Q004D00012Q003A000200013Q0020CB00020002000D00060F0002004D00013Q0004D03Q004D00012Q003A000200013Q0020D200020002000D00202Q00030002000F00102Q0001000E000300202Q00030002001100102Q00010010000300202Q00030002001300102Q00010012000300202Q00030002001500102Q00010014000300202Q00030002001700107A0001001600030020CB00030002001900107A0001001800032Q008100016Q00A62Q0100014Q00BA3Q00017Q00193Q0003093Q0043686172616374657203063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q00426173655061727403053Q00436F6C6F72030B3Q005370656369616C4D657368030B3Q00566572746578436F6C6F7203053Q00446563616C03073Q005465787475726503063Q00436F6C6F723303153Q0046696E6446697273744368696C644F66436C612Q73030A3Q00426F6479436F6C6F727303043Q0048656164030A3Q0048656164436F6C6F723303053Q00546F72736F030B3Q00546F72736F436F6C6F723303073Q004C65667441726D030D3Q004C65667441726D436F6C6F723303083Q00526967687441726D030E3Q00526967687441726D436F6C6F723303073Q004C6566744C6567030D3Q004C6566744C6567436F6C6F723303083Q0052696768744C6567030E3Q0052696768744C6567436F6C6F723300424Q0070019Q009Q002Q00013Q00206Q000100064Q0007000100010004D03Q000700012Q00BA3Q00013Q0012572Q0100023Q00204401023Q00032Q002D000200034Q00132Q013Q00030004D03Q002B000100204401060005000400128E010800054Q009000060008000200060F0006001500013Q0004D03Q001500012Q003A00065Q0020CB0007000500062Q00E60006000500070004D03Q002B000100204401060005000400128E010800074Q009000060008000200060F0006001E00013Q0004D03Q001E00012Q003A00065Q0020CB0007000500082Q00E60006000500070004D03Q002B000100204401060005000400128E010800094Q009000060008000200065801060028000100010004D03Q0028000100204401060005000400128E0108000A4Q009000060008000200060F0006002B00013Q0004D03Q002B00012Q003A00065Q0020CB00070005000B2Q00E60006000500070006482Q01000C000100020004D03Q000C00010020442Q013Q000C00128E0103000D4Q009000010003000200060F0001004100013Q0004D03Q004100012Q003A00026Q008100033Q00060020CB00040001000F00107A0003000E00040020CB00040001001100107A0003001000040020CB00040001001300107A0003001200040020CB00040001001500107A0003001400040020CB00040001001700107A0003001600040020CB00040001001900107A00030018000400107A0002000D00032Q00BA3Q00017Q00103Q0003013Q005203013Q004703013Q004203073Q00566563746F72332Q033Q006E6577026Q00F03F03063Q00506172656E7403053Q00436F6C6F72030B3Q00566572746578436F6C6F7203063Q00436F6C6F7233030A3Q0048656164436F6C6F7233030B3Q00546F72736F436F6C6F7233030D3Q004C65667441726D436F6C6F7233030E3Q00526967687441726D436F6C6F7233030D3Q004C6566744C6567436F6C6F7233030E3Q0052696768744C6567436F6C6F7233014B4Q003A00015Q00060F0001000400013Q0004D03Q000400012Q00BA3Q00013Q0020CB00013Q000100209600023Q000200202Q00033Q000300122Q000400043Q00202Q0004000400054Q000500016Q000600026Q000700036Q00040007000200122Q000500066Q000600016Q000600063Q00122Q000700063Q00042Q0005001B00012Q003A000900014Q00D100090009000800060F0009001A00013Q0004D03Q001A00010020CB000A0009000700060F000A001A00013Q0004D03Q001A000100107A000900083Q0004F500050012000100128E010500064Q003A000600024Q005B000600063Q00128E010700063Q0004CD0005002900012Q003A000900024Q00D100090009000800060F0009002800013Q0004D03Q002800010020CB000A0009000700060F000A002800013Q0004D03Q0028000100107A0009000900040004F500050020000100128E010500064Q003A000600034Q005B000600063Q00128E010700063Q0004CD0005003700012Q003A000900034Q00D100090009000800060F0009003600013Q0004D03Q003600010020CB000A0009000700060F000A003600013Q0004D03Q0036000100107A0009000A3Q0004F50005002E00012Q003A000500043Q00060F0005004A00013Q0004D03Q004A00012Q003A000500043Q0020CB00050005000700060F0005004A00013Q0004D03Q004A00012Q003A000500043Q0010190105000B6Q000500043Q00102Q0005000C6Q000500043Q00102Q0005000D6Q000500043Q00102Q0005000E6Q000500043Q00102Q0005000F6Q000500043Q00102Q000500104Q00BA3Q00017Q00113Q0003063Q004E6F7469667903053Q005469746C6503063Q0053797374656D03073Q00436F6E74656E7403193Q005261696E626F7720417661746172204163746976617465642103083Q004475726174696F6E026Q00084003043Q007461736B03063Q0063616E63656C030A3Q00446973636F2Q6E65637403093Q00436861726163746572030E3Q00436861726163746572412Q64656403073Q00436F2Q6E656374028Q0003093Q0048656172746265617403043Q0077616974031B3Q005261696E626F77204176617461722044656163746976617465642E01604Q00A6017Q003A00015Q00060F0001003D00013Q0004D03Q003D00012Q003A000100013Q0020A00001000100014Q00033Q000300302Q00030002000300302Q00030004000500302Q0003000600074Q0001000300014Q000100023Q00062Q0001001400013Q0004D03Q001400010012572Q0100083Q0020142Q01000100094Q000200026Q0001000200014Q000100016Q000100024Q003A000100033Q00060F0001001C00013Q0004D03Q001C00012Q003A000100033Q0020442Q010001000A2Q009A0001000200012Q009D2Q0100014Q00A62Q0100034Q003A000100044Q00830001000100014Q000100056Q000200063Q00202Q00020002000B4Q0001000200014Q000100063Q00202Q00010001000C00202Q00010001000D00067900033Q000100052Q003A8Q003A3Q00074Q003A3Q00084Q003A3Q00044Q003A3Q00054Q009C2Q01000300024Q000100033Q00122Q0001000E3Q00122Q0002000E6Q000300093Q00202Q00030003000F00202Q00030003000D00067900050001000100062Q003A8Q0082012Q00024Q003A3Q00064Q003A3Q00074Q0082012Q00014Q003A3Q000A4Q00900003000500022Q00A6010300024Q00802Q015Q0004D03Q005F00012Q007100016Q00A62Q016Q003A000100023Q00060F0001004700013Q0004D03Q004700012Q003A000100023Q0020442Q010001000A2Q009A0001000200012Q009D2Q0100014Q00A62Q0100024Q003A000100033Q00060F0001004F00013Q0004D03Q004F00012Q003A000100033Q0020442Q010001000A2Q009A0001000200012Q009D2Q0100014Q00A62Q0100034Q007100016Q00362Q0100076Q000100086Q00010001000100122Q000100083Q00202Q0001000100104Q0001000100014Q0001000B6Q0001000100014Q000100013Q00202Q0001000100014Q00033Q000300302Q00030002000300302Q00030004001100302Q0003000600074Q0001000300012Q00BA3Q00013Q00023Q00063Q00030C3Q0057616974466F724368696C6403103Q0048756D616E6F6964522Q6F7450617274026Q00244003043Q007461736B03043Q0077616974026Q00E03F01173Q0020A900013Q000100122Q000300023Q00122Q000400036Q0001000400014Q00015Q00062Q0001001600013Q0004D03Q001600012Q0071000100014Q00A62Q0100014Q003A000100024Q002B0001000100010012572Q0100043Q0020CB00010001000500128E010200064Q009A0001000200012Q003A000100034Q002B0001000100012Q003A000100044Q008201026Q009A0001000200012Q007100016Q00A62Q0100014Q00BA3Q00017Q00073Q00026Q00F03F027Q0040028Q0003093Q0043686172616374657203063Q00436F6C6F723303073Q0066726F6D48535602FA7E6ABC7493683F00224Q003A7Q000658012Q0004000100010004D03Q000400012Q00BA3Q00014Q003A3Q00013Q0020A65Q00012Q00A6012Q00014Q003A3Q00013Q002606012Q000B000100020004D03Q000B00012Q00BA3Q00013Q00128E012Q00034Q00A6012Q00014Q003A3Q00023Q0020CB5Q000400060F3Q002100013Q0004D03Q002100012Q003A000100033Q0006582Q010021000100010004D03Q002100010012572Q0100053Q0020CC0001000100064Q000200043Q00122Q000300013Q00122Q000400016Q0001000400024Q000200056Q000300016Q0002000200014Q000200043Q00202Q00020002000700202Q0002000200014Q000200044Q00BA3Q00017Q00013Q0003063Q00697061697273010D3Q0012572Q0100014Q003A00026Q00FC0001000200030004D03Q0008000100066D012Q0008000100050004D03Q000800012Q0071000600014Q00DD000600023Q0006482Q010004000100020004D03Q000400012Q007100016Q00DD000100024Q00BA3Q00017Q000E3Q0003063Q004E6F7469667903053Q005469746C6503063Q0053797374656D03073Q00436F6E74656E7403193Q00496E66696E69746520536C696465204163746976617465642103083Q004475726174696F6E026Q000840030A3Q00446973636F2Q6E656374028Q00030A3Q00496E707574426567616E03073Q00436F2Q6E656374030A3Q00496E707574456E64656403093Q00486561727462656174031B3Q00496E66696E69746520536C6964652044656163746976617465642E016C4Q00A6017Q003A00015Q00060F0001004600013Q0004D03Q004600012Q003A000100013Q0020A00001000100014Q00033Q000300302Q00030002000300302Q00030004000500302Q0003000600074Q0001000300014Q000100023Q00062Q0001001300013Q0004D03Q001300012Q003A000100023Q0020442Q01000100082Q009A0001000200012Q009D2Q0100014Q00A62Q0100024Q003A000100033Q00060F0001001B00013Q0004D03Q001B00012Q003A000100033Q0020442Q01000100082Q009A0001000200012Q009D2Q0100014Q00A62Q0100034Q003A000100043Q00060F0001002300013Q0004D03Q002300012Q003A000100043Q0020442Q01000100082Q009A0001000200012Q009D2Q0100014Q00A62Q0100043Q00128E2Q0100094Q0029000100056Q00018Q000100066Q000100073Q00202Q00010001000A00202Q00010001000B00067900033Q000100032Q003A3Q00084Q003A3Q00064Q003A3Q00054Q006B0001000300024Q000100036Q000100073Q00202Q00010001000C00202Q00010001000B00067900030001000100032Q003A3Q00084Q003A3Q00064Q003A3Q00054Q006B0001000300024Q000100046Q000100093Q00202Q00010001000D00202Q00010001000B00067900030002000100062Q003A8Q003A3Q00064Q003A3Q000A4Q003A3Q00054Q003A3Q000B4Q003A3Q000C4Q00900001000300022Q00A62Q0100023Q0004D03Q006B00012Q007100016Q00B400018Q00018Q000100063Q00122Q000100096Q000100056Q000100023Q00062Q0001005400013Q0004D03Q005400012Q003A000100023Q0020442Q01000100082Q009A0001000200012Q009D2Q0100014Q00A62Q0100024Q003A000100033Q00060F0001005C00013Q0004D03Q005C00012Q003A000100033Q0020442Q01000100082Q009A0001000200012Q009D2Q0100014Q00A62Q0100034Q003A000100043Q00060F0001006400013Q0004D03Q006400012Q003A000100043Q0020442Q01000100082Q009A0001000200012Q009D2Q0100014Q00A62Q0100044Q003A000100013Q0020612Q01000100014Q00033Q000300302Q00030002000300302Q00030004000E00302Q0003000600074Q0001000300012Q00BA3Q00013Q00033Q00023Q0003073Q004B6579436F6465028Q00020D3Q00060F0001000300013Q0004D03Q000300012Q00BA3Q00014Q003A00025Q0020CB00033Q00012Q001F01020002000200060F0002000C00013Q0004D03Q000C00012Q0071000200014Q00A6010200013Q00128E010200024Q00A6010200024Q00BA3Q00017Q00023Q0003073Q004B6579436F6465028Q00020A4Q003A00025Q0020CB00033Q00012Q001F01020002000200060F0002000900013Q0004D03Q000900012Q007100026Q00A6010200013Q00128E010200024Q00A6010200024Q00BA3Q00017Q00183Q0003093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F6964030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q00476574537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503043Q004465616403043Q006D6174682Q033Q006D696E03073Q00566563746F72332Q033Q006E657703063Q00434672616D65030A3Q004C2Q6F6B566563746F7203013Q0058028Q0003013Q005A03093Q004D61676E6974756465027B14AE47E17A843F03043Q00556E697403163Q00412Q73656D626C794C696E65617256656C6F6369747903013Q0059030F3Q005365744E6574776F726B4F776E657200484Q003A7Q000658012Q0004000100010004D03Q000400012Q00BA3Q00014Q003A3Q00013Q000658012Q0008000100010004D03Q000800012Q00BA3Q00014Q003A3Q00023Q0020CB5Q0001000658012Q000D000100010004D03Q000D00012Q00BA3Q00013Q0020442Q013Q0002001291000300036Q00010003000200202Q00023Q000400122Q000400056Q00020004000200062Q0001001700013Q0004D03Q0017000100065801020018000100010004D03Q001800012Q00BA3Q00013Q0020440103000100062Q00FE00030002000200122Q000400073Q00202Q00040004000800202Q00040004000900062Q00030020000100040004D03Q002000012Q00BA3Q00013Q0012570103000A3Q00209900030003000B4Q000400036Q000500046Q0004000400054Q000500056Q0003000500024Q000300033Q00122Q0003000C3Q00202Q00030003000D00202Q00040002000E00202Q00040004000F00202Q00040004001000122Q000500113Q00202Q00060002000E00202Q00060006000F00202Q0006000600124Q00030006000200202Q00040003001300262Q00040036000100140004D03Q003600012Q00BA3Q00013Q0020CB00030003001500200E01040002001600202Q00040004001700122Q0005000C3Q00202Q00050005000D00202Q0006000300104Q000700036Q0006000600074Q000700043Q00202Q0008000300124Q000900036Q0008000800094Q00050008000200102Q00020016000500202Q0005000200184Q000700076Q0005000700016Q00017Q00073Q00030C3Q00476574412Q747269627574652Q033Q0054616700030E3Q0046696E6446697273744368696C642Q033Q0049734103093Q0056616C75654261736503053Q0056616C756501193Q000658012Q0004000100010004D03Q000400012Q009D2Q0100014Q00DD000100023Q0020442Q013Q000100128E010300024Q009000010003000200266A2Q01000A000100030004D03Q000A00012Q00DD000100023Q00204401023Q000400128E010400024Q009000020004000200060F0002001600013Q0004D03Q0016000100204401030002000500128E010500064Q009000030005000200060F0003001600013Q0004D03Q001600010020CB0003000200072Q00DD000300024Q009D010300034Q00DD000300024Q00BA3Q00017Q00023Q0003043Q007461736B03053Q00737061776E000B4Q00EB9Q009Q003Q00013Q00124Q00013Q00206Q000200067900013Q000100032Q003A3Q00024Q003A8Q003A3Q00034Q009A3Q000200012Q00BA3Q00013Q00013Q000D3Q0003043Q007469636B026Q00244003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C6403043Q0047616D6503073Q00506C617965727303043Q004E616D6503083Q00746F6E756D626572028Q00025Q00E06F4003043Q007461736B03043Q0077616974026Q00E03F00373Q001257012Q00014Q009F012Q000100020012572Q0100014Q009F2Q01000100022Q0055000100013Q0026062Q010036000100020004D03Q003600010012572Q0100033Q0020442Q010001000400128E010300054Q009000010003000200060F0001003100013Q0004D03Q003100010012572Q0100033Q00202200010001000500202Q00010001000400122Q000300066Q00010003000200062Q0001003100013Q0004D03Q003100010012572Q0100033Q00201D00010001000500202Q00010001000600202Q0001000100044Q00035Q00202Q0003000300074Q00010003000200062Q0001003100013Q0004D03Q003100012Q003A000200024Q0054000300016Q0002000200024Q000200016Q000200013Q00062Q0002003100013Q0004D03Q00310001001257010200084Q003A000300014Q001F01020002000200060F0002002F00013Q0004D03Q002F0001000E5D0009002F000100020004D03Q002F00010026390002002F0001000A0004D03Q002F00010004D03Q003600010004D03Q003100012Q009D010300034Q00A6010300013Q0012572Q01000B3Q0020CB00010001000C00128E0102000D4Q009A0001000200010004D03Q000200012Q00BA3Q00017Q000B3Q0003083Q00746F6E756D626572028Q00025Q00E06F40034Q0003063Q0062752Q66657203063Q00637265617465027Q004003073Q0077726974657538026Q00F03F026Q003140030A3Q00666972657369676E616C01334Q003A00015Q0006582Q010004000100010004D03Q000400012Q00BA3Q00013Q0012572Q0100014Q003A00026Q001F2Q010002000200060F0001000D00013Q0004D03Q000D00010026530001000D000100020004D03Q000D0001000E2C0003000E000100010004D03Q000E00012Q00BA3Q00014Q003A000200014Q00D1000200023Q00060F0002001600013Q0004D03Q001600012Q003A000200014Q00D1000200023Q00265401020017000100040004D03Q001700012Q00BA3Q00013Q001257010200053Q00207701020002000600122Q000300076Q00020002000200122Q000300053Q00202Q0003000300084Q000400023Q00122Q000500026Q000600016Q00030006000100122Q000300053Q0020CB0003000300082Q00A8000400023Q00122Q000500093Q00122Q0006000A6Q0003000600014Q000300023Q00062Q0003003200013Q0004D03Q003200010012570103000B4Q0012000400026Q000500026Q000600016Q000700016Q000700076Q0006000100012Q00A20103000600012Q00BA3Q00017Q00033Q0003043Q007461736B03043Q0077616974029A5Q99B93F000F4Q003A00015Q0006582Q010004000100010004D03Q000400012Q00BA3Q00014Q003A00016Q009C000200026Q00025Q00122Q000200013Q00202Q00020002000200122Q000300036Q0002000200014Q000200016Q000300016Q0002000200016Q00017Q00033Q00030E3Q00682Q6F6B6D6574616D6574686F6403043Q0067616D65030A3Q002Q5F6E616D6563612Q6C000D3Q001257012Q00013Q0012572Q0100023Q00128E010200033Q00067900033Q000100062Q003A8Q003A3Q00014Q003A3Q00024Q003A3Q00034Q003A3Q00044Q003A3Q00054Q00BE3Q00034Q00CE8Q00BA3Q00013Q00013Q000B3Q0003113Q006765746E616D6563612Q6C6D6574686F64030B3Q00636865636B63612Q6C6572030A3Q004669726553657276657203043Q0074797065026Q00F03F03063Q00737472696E67026Q002840034Q0003043Q007461736B03053Q0064656C6179029A5Q99B93F01374Q008100026Q002D01036Q002A01023Q0001001257010300014Q009F010300010002001257010400024Q009F01040001000200065801040031000100010004D03Q0031000100265401030031000100030004D03Q003100012Q003A00045Q00066D012Q0031000100040004D03Q00310001001257010400043Q0020CB0005000200052Q001F01040002000200265401040031000100060004D03Q0031000100128E010400053Q00128E010500073Q00128E010600053Q0004CD0004003100012Q003A000800014Q00D100080008000700060F0008002F00013Q0004D03Q002F00012Q003A000800024Q00D100080008000700266A0108002F000100080004D03Q002F00010020CB0008000200052Q003A000900024Q00D100090009000700066D0108002F000100090004D03Q002F00012Q00A6010700033Q001257010800093Q0020CB00080008000A00128E0109000B3Q000679000A3Q000100032Q003A3Q00034Q0082012Q00074Q003A3Q00044Q00A20108000A00012Q009D010800084Q00DD000800024Q008001075Q0004F50004001700012Q003A000400054Q006300058Q00068Q00048Q00049Q0000013Q00018Q000A4Q003A8Q003A000100013Q00066D012Q0009000100010004D03Q000900012Q009D017Q00A6017Q003A3Q00024Q003A000100014Q009A3Q000200012Q00BA3Q00017Q00033Q0003043Q007461736B03043Q0077616974026Q00F03F00073Q0012923Q00013Q00206Q000200122Q000100038Q000200019Q006Q000100016Q00017Q00023Q00030C3Q00536574412Q7472696275746503083Q00456D6F74654E756D01073Q00060F3Q000600013Q0004D03Q000600010020442Q013Q000100128E010300024Q003A00046Q00A22Q01000400012Q00BA3Q00017Q00033Q0003083Q00746F6E756D626572026Q00F03F03093Q0043686172616374657201103Q0012572Q0100014Q008201026Q001F2Q01000200020006582Q010006000100010004D03Q0006000100128E2Q0100024Q00A62Q016Q003A000100013Q0020CB00010001000300060F0001000F00013Q0004D03Q000F00012Q003A000100024Q003A000200013Q0020CB0002000200032Q009A0001000200012Q00BA3Q00017Q00033Q0003043Q007461736B03043Q0077616974026Q00F03F01083Q0012032Q0100013Q00202Q00010001000200122Q000200036Q0001000200014Q00018Q00028Q0001000200016Q00017Q00063Q0003043Q007461736B03043Q0077616974027Q004003093Q00436861726163746572030C3Q00476574412Q7472696275746503083Q00456D6F74654E756D00163Q001257012Q00013Q0020145Q000200122Q000100038Q000200019Q0000206Q000400066Q00013Q0004D05Q00012Q003A7Q002Q205Q000400206Q000500122Q000200068Q000200024Q000100013Q00066Q000100010004D05Q00012Q003A3Q00024Q003A00015Q0020CB0001000100042Q009A3Q000200010004D05Q00012Q00BA3Q00017Q00033Q0003043Q00677375622Q033Q0025732B034Q0001084Q000900018Q000200013Q00202Q00033Q000100122Q000500023Q00122Q000600036Q0003000600024Q0001000200036Q00017Q00033Q0003043Q00677375622Q033Q0025732B034Q0001084Q000900018Q000200013Q00202Q00033Q000100122Q000500023Q00122Q000600036Q0003000600024Q0001000200036Q00017Q000D3Q00026Q00F03F026Q002840034Q0003063Q004E6F7469667903053Q005469746C65030D3Q00456D6F7465204368616E67657203073Q00436F6E74656E7403163Q00506C65617365205479706520456D6F7465204E616D6503083Q004475726174696F6E026Q00084003053Q006C6F77657203143Q0055706461746520456D6F7465204368616E676572026Q00144000454Q008F7Q00122Q000100013Q00122Q000200023Q00122Q000300013Q00042Q0001001000012Q003A00056Q00D10005000500040026540105000D000100030004D03Q000D00012Q003A000500014Q00D100050005000400266A0105000F000100030004D03Q000F00012Q00713Q00013Q0004D03Q001000010004F5000100050001000658012Q001A000100010004D03Q001A00012Q003A000100023Q0020612Q01000100044Q00033Q000300302Q00030005000600302Q00030007000800302Q00030009000A4Q0001000300012Q00BA3Q00013Q0002222Q015Q00067900020001000100022Q0082012Q00014Q003A3Q00033Q00128E010300013Q00128E010400023Q00128E010500013Q0004CD0003003D00012Q0082010700024Q00FA00088Q0008000800064Q0007000200024Q000800026Q000900016Q0009000900064Q0008000200024Q000900043Q00062Q000A003B000100070004D03Q003B000100069E000A003B000100080004D03Q003B00012Q003A000A6Q008A010A000A000600202Q000A000A000B4Q000A000200024Q000B00016Q000B000B000600202Q000B000B000B4Q000B0002000200062Q000A003A0001000B0004D03Q003A00012Q003F010A6Q0071000A00014Q00E600090006000A0004F50003002200012Q003A000300023Q0020610103000300044Q00053Q000300302Q00050005000600302Q00050007000C00302Q00050009000D4Q0003000500012Q00BA3Q00013Q00023Q00043Q0003043Q00677375622Q033Q0025732B034Q0003053Q006C6F77657201083Q00206A00013Q000100122Q000300023Q00122Q000400036Q00010004000200202Q0001000100044Q000100026Q00019Q0000017Q00093Q00034Q00030E3Q0046696E6446697273744368696C6403053Q004974656D7303063Q00456D6F74657303063Q00697061697273030B3Q004765744368696C6472656E2Q033Q00497341030C3Q004D6F64756C6553637269707403043Q004E616D6501293Q002654012Q0004000100010004D03Q000400012Q007100016Q00DD000100024Q003A00016Q009B00028Q0001000200024Q000200013Q00202Q00020002000200122Q000400036Q00020004000200062Q0002001100013Q0004D03Q0011000100204401030002000200128E010500044Q00900003000500022Q0082010200033Q00060F0002002600013Q0004D03Q00260001001257010300053Q0020440104000200062Q002D000400054Q001301033Q00050004D03Q0024000100204401080007000700128E010A00084Q00900008000A000200060F0008002400013Q0004D03Q002400012Q003A00085Q0020CB0009000700092Q001F01080002000200066D01080024000100010004D03Q002400012Q0071000800014Q00DD000800023Q00064801030018000100020004D03Q001800012Q007100036Q00DD000300024Q00BA3Q00017Q000C3Q00026Q00F03F026Q002840034Q00010003083Q0053657456616C756503063Q004E6F7469667903053Q005469746C65030D3Q00456D6F7465204368616E67657203073Q00436F6E74656E74030F3Q00526573657420412Q6C20456D6F746503083Q004475726174696F6E026Q000840002F3Q00128E012Q00013Q00128E2Q0100023Q00128E010200013Q0004CD3Q002700012Q003A00045Q00201C0104000300034Q000400013Q00202Q0004000300034Q000400023Q00202Q0004000300044Q000400036Q00040004000300062Q0004001800013Q0004D03Q001800012Q003A000400034Q00D10004000400030020CB00040004000500060F0004001800013Q0004D03Q001800012Q003A000400034Q00D100040004000300204401040004000500128E010600034Q00A20104000600012Q003A000400044Q00D100040004000300060F0004002600013Q0004D03Q002600012Q003A000400044Q00D10004000400030020CB00040004000500060F0004002600013Q0004D03Q002600012Q003A000400044Q00D100040004000300204401040004000500128E010600034Q00A20104000600010004F53Q000400012Q003A3Q00053Q002061014Q00064Q00023Q000300302Q00020007000800302Q00020009000A00302Q0002000B000C6Q000200012Q00BA3Q00017Q00043Q00030E3Q0046696E6446697273744368696C6403063Q004576656E747303053Q00456D6F746503053Q007063612Q6C001B4Q004D016Q00206Q000100122Q000200028Q0002000200064Q000B00013Q0004D03Q000B00012Q003A7Q0020CB5Q0002002044014Q000100128E010200034Q00903Q0002000200060F3Q001000013Q0004D03Q001000012Q003A000100013Q00060F0001001100013Q0004D03Q001100012Q00BA3Q00013Q0012572Q0100043Q00067900023Q000100062Q0082017Q003A3Q00024Q003A3Q00034Q003A3Q00044Q003A8Q003A3Q00014Q009A0001000200012Q00BA3Q00013Q00013Q00043Q00030F3Q006765747261776D6574617461626C6503043Q0067616D65030A3Q002Q5F6E616D6563612Q6C030B3Q00736574726561646F6E6C7900173Q001295012Q00013Q00122Q000100028Q0002000200202Q00013Q000300122Q000200046Q00038Q00048Q00020004000100067900023Q000100062Q003A8Q003A3Q00014Q003A3Q00024Q003A3Q00034Q003A3Q00044Q0082012Q00013Q001020012Q0003000200122Q000200046Q00038Q000400016Q0002000400014Q000200016Q000200058Q00013Q00013Q000C3Q0003113Q006765746E616D6563612Q6C6D6574686F64030A3Q004669726553657276657203083Q00746F6E756D626572026Q00F03F026Q00204003093Q00436861726163746572030C3Q00476574412Q747269627574652Q033Q0054616703053Q00456D6F7465030A3Q00666972657369676E616C03063Q004576656E7473030D3Q004F6E436C69656E744576656E74013E3Q001278010200016Q0002000100024Q00038Q00048Q00033Q000100265401020038000100020004D03Q003800012Q003A00045Q00066D012Q0038000100040004D03Q00380001001257010400033Q0020CB0005000300042Q001F0104000200022Q003A000500013Q00060F0005003800013Q0004D03Q0038000100060F0004003800013Q0004D03Q00380001000E5D00040038000100040004D03Q0038000100263900040038000100050004D03Q003800012Q003A000500023Q0020CB00050005000600060F0005001F00013Q0004D03Q001F00012Q003A000500023Q0020CB00050005000600204401050005000700128E010700084Q00900005000700022Q003A000600034Q00D100060006000400065801060029000100010004D03Q002900012Q003A000600023Q00204401060006000700128E010800094Q0082010900044Q003B0108000800092Q009000060008000200060F0005003600013Q0004D03Q0036000100060F0006003600013Q0004D03Q003600010012570107000A4Q00E1000800043Q00202Q00080008000B00202Q00080008000600202Q00080008000900202Q00080008000C4Q000900056Q000A00066Q0007000A00012Q009D010700074Q00DD000700024Q003A000400054Q006300058Q00068Q00048Q00049Q0000019Q002Q0001044Q003A00016Q003A000200014Q00E6000100024Q00BA3Q00017Q000A3Q0003053Q007061697273030C3Q00536574412Q7472696275746503053Q00456D6F746503063Q004E6F7469667903053Q005469746C65030D3Q00456D6F7465204368616E67657203073Q00436F6E74656E7403103Q00412Q706C69656420284C65676163792903083Q004475726174696F6E026Q00084000194Q002C012Q00019Q003Q00124Q00016Q000100018Q0002000200044Q000D00012Q003A000500023Q00204101050005000200122Q000700036Q000800036Q0007000700084Q000800046Q000500080001000648012Q0006000100020004D03Q000600012Q003A3Q00034Q0094012Q000100016Q00043Q00206Q00044Q00023Q000300302Q00020005000600302Q00020007000800302Q00020009000A6Q000200016Q00017Q000E3Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403083Q00476574537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503043Q0044656164028Q0003043Q007469636B030A3Q00446973636F2Q6E65637403093Q0048656172746265617403073Q00436F2Q6E65637401394Q003A00015Q00060F0001000400013Q0004D03Q000400012Q00BA3Q00014Q003A000100013Q0020CB0001000100010006582Q010009000100010004D03Q000900012Q00BA3Q00013Q00204401020001000200128E010400034Q00900002000400020006580102000F000100010004D03Q000F00012Q00BA3Q00013Q00204401030001000400128E010500054Q009000030005000200065801030015000100010004D03Q001500012Q00BA3Q00013Q0020440104000300062Q00FE00040002000200122Q000500073Q00202Q00050005000800202Q00050005000900062Q0004001D000100050004D03Q001D00012Q00BA3Q00014Q0071000400014Q006001045Q00122Q0004000A6Q00055Q00122Q0006000B6Q0006000100024Q000700023Q00062Q0007002B00013Q0004D03Q002B00012Q003A000700023Q00204401070007000C2Q009A0007000200012Q009D010700074Q00A6010700024Q003A000700033Q0020CB00070007000D00204401070007000E00067900093Q000100072Q003A8Q003A3Q00024Q003A3Q00014Q0082012Q00064Q003A3Q00044Q0082012Q00054Q0082012Q00044Q00900007000900022Q00A6010700024Q00BA3Q00013Q00013Q00103Q00030A3Q00446973636F2Q6E65637403093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403043Q007469636B03043Q006D6174682Q033Q006D696E026Q00F03F027Q004003063Q00434672616D6503083Q00506F736974696F6E03103Q00546F45756C6572416E676C657359585A2Q033Q006E657703063Q00416E676C6573028Q002Q033Q00726164014B4Q003A00015Q0006582Q010009000100010004D03Q000900012Q003A000100013Q0020442Q01000100012Q009A0001000200012Q009D2Q0100014Q00A62Q0100014Q00BA3Q00014Q003A000100023Q0020CB00010001000200069E00020010000100010004D03Q0010000100204401020001000300128E010400044Q00900002000400020006580102001A000100010004D03Q001A00012Q007100036Q004000038Q000300013Q00202Q0003000300014Q0003000200014Q000300036Q000300014Q00BA3Q00013Q001257010300054Q00040003000100024Q000400036Q00030003000400122Q000400063Q00202Q0004000400074Q000500046Q00050003000500122Q000600086Q00040006000200102Q00050008000400202Q00050005000900102Q0005000800054Q000600056Q0006000600054Q000700066Q0007000600074Q000600063Q00202Q00080002000A00202Q00080008000B00202Q00090002000A00202Q00090009000C4Q00090002000B00122Q000C000A3Q00202Q000C000C000D4Q000D00086Q000C0002000200122Q000D000A3Q00202Q000D000D000E00122Q000E000F3Q00122Q000F00063Q00202Q000F000F00104Q001000076Q000F000200024Q000F000A000F00122Q0010000F6Q000D001000024Q000C000C000D00102Q0002000A000C000E2Q0008004A000100040004D03Q004A00012Q0071000C6Q0040000C8Q000C00013Q00202Q000C000C00014Q000C000200014Q000C000C6Q000C00014Q00BA3Q00017Q000B3Q0003063Q004E6F7469667903053Q005469746C6503063Q0053797374656D03073Q00436F6E74656E7403123Q0033363020486F70204163746976617465642103083Q004475726174696F6E026Q000840030A3Q00446973636F2Q6E656374030A3Q00496E707574426567616E03073Q00436F2Q6E65637403143Q0033363020486F702044656163746976617465642E01504Q00A6017Q003A00015Q00060F0001002C00013Q0004D03Q002C00012Q003A000100013Q0020A00001000100014Q00033Q000300302Q00030002000300302Q00030004000500302Q0003000600074Q0001000300014Q000100023Q00062Q0001001300013Q0004D03Q001300012Q003A000100023Q0020442Q01000100082Q009A0001000200012Q009D2Q0100014Q00A62Q0100024Q003A000100033Q00060F0001001B00013Q0004D03Q001B00012Q003A000100033Q0020442Q01000100082Q009A0001000200012Q009D2Q0100014Q00A62Q0100034Q003A000100043Q0020CB0001000100090020442Q010001000A00067900033Q000100022Q003A8Q003A3Q00054Q006B0001000300024Q000100026Q000100043Q00202Q00010001000900202Q00010001000A00067900030001000100022Q003A8Q003A3Q00054Q00900001000300022Q00A62Q0100033Q0004D03Q004F00012Q007100016Q00672Q018Q00018Q000100066Q000100073Q00062Q0001003800013Q0004D03Q003800012Q003A000100073Q0020442Q01000100082Q009A0001000200012Q009D2Q0100014Q00A62Q0100074Q003A000100023Q00060F0001004000013Q0004D03Q004000012Q003A000100023Q0020442Q01000100082Q009A0001000200012Q009D2Q0100014Q00A62Q0100024Q003A000100033Q00060F0001004800013Q0004D03Q004800012Q003A000100033Q0020442Q01000100082Q009A0001000200012Q009D2Q0100014Q00A62Q0100034Q003A000100013Q0020612Q01000100014Q00033Q000300302Q00030002000300302Q00030004000B00302Q0003000600074Q0001000300012Q00BA3Q00013Q00023Q00043Q0003073Q004B6579436F646503043Q00456E756D03013Q0041025Q0080664002113Q00060F0001000300013Q0004D03Q000300012Q00BA3Q00014Q003A00025Q00065801020007000100010004D03Q000700012Q00BA3Q00013Q0020CB00023Q0001001257010300023Q0020CB0003000300010020CB00030003000300066D01020010000100030004D03Q001000012Q003A000200013Q00128E010300044Q009A0002000200012Q00BA3Q00017Q00043Q0003073Q004B6579436F646503043Q00456E756D03013Q0044025Q0080664002113Q00060F0001000300013Q0004D03Q000300012Q00BA3Q00014Q003A00025Q00065801020007000100010004D03Q000700012Q00BA3Q00013Q0020CB00023Q0001001257010300023Q0020CB0003000300010020CB00030003000300066D01020010000100030004D03Q001000012Q003A000200013Q00128E010300044Q009A0002000200012Q00BA3Q00017Q00033Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727400094Q003A7Q0020CB5Q000100069E0001000700013Q0004D03Q000700010020442Q013Q000200128E010300034Q00900001000300022Q00DD000100024Q00BA3Q00017Q00033Q0003093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696400094Q003A7Q0020CB5Q000100069E0001000700013Q0004D03Q000700010020442Q013Q000200128E010300034Q00900001000300022Q00DD000100024Q00BA3Q00017Q00103Q00030D3Q0052617963617374506172616D732Q033Q006E6577031A3Q0046696C74657244657363656E64616E7473496E7374616E63657303093Q00436861726163746572030A3Q0046696C7465725479706503043Q00456E756D03113Q005261796361737446696C7465725479706503073Q004578636C75646503063Q00434672616D65030A3Q004C2Q6F6B566563746F72030B3Q005269676874566563746F7203063Q0069706169727303093Q00776F726B737061636503073Q005261796361737403083Q00506F736974696F6E03063Q004E6F726D616C012E3Q001267000100013Q00202Q0001000100024Q0001000100024Q000200016Q00035Q00202Q0003000300044Q00020001000100107A000100030002001257010200063Q0020CB0002000200070020CB00020002000800107A0001000500022Q0081000200043Q0020CB00033Q00090020CB00030003000A0020CB00043Q00090020CB00040004000A2Q003E000400043Q0020CB00053Q000900203500050005000B00202Q00063Q000900202Q00060006000B4Q000600066Q0002000400010012570103000C4Q0082010400024Q00FC0003000200050004D03Q002800010012570108000D3Q00200D01080008000E00202Q000A3Q000F4Q000B00016Q000B0007000B4Q000C00016Q0008000C000200062Q0008002800013Q0004D03Q002800012Q0071000900013Q0020CB000A000800102Q0024000900033Q0006480103001C000100020004D03Q001C00012Q007100036Q009D010400044Q0024000300034Q00BA3Q00017Q000F3Q0003063Q004E6F7469667903053Q005469746C6503063Q0053797374656D03073Q00436F6E74656E7403153Q00506978656C2053757266204163746976617465642103083Q004475726174696F6E026Q000840030A3Q00496E707574426567616E03073Q00436F2Q6E656374030A3Q00496E707574456E64656403093Q00486561727462656174030D3Q00506C6174666F726D5374616E640100030A3Q00446973636F2Q6E65637403173Q00506978656C20537572662044656163746976617465642E015D4Q00A6017Q003A00015Q00060F0001003000013Q0004D03Q003000012Q003A000100013Q0020612Q01000100014Q00033Q000300302Q00030002000300302Q00030004000500302Q0003000600074Q0001000300012Q00F900018Q000100026Q00018Q000100036Q000100016Q000100046Q000100063Q00202Q00010001000800202Q00010001000900067900033Q000100012Q003A3Q00034Q006B0001000300024Q000100056Q000100063Q00202Q00010001000A00202Q00010001000900067900030001000100042Q003A3Q00034Q003A3Q00024Q003A3Q00044Q003A3Q00084Q006B0001000300024Q000100076Q0001000A3Q00202Q00010001000B00202Q00010001000900067900030002000100072Q003A8Q003A3Q000B4Q003A3Q00084Q003A3Q00024Q003A3Q000C4Q003A3Q00034Q003A3Q00044Q00900001000300022Q00A62Q0100093Q0004D03Q005C00012Q007100016Q001A00018Q00018Q000100026Q00018Q000100036Q000100016Q000100046Q000100086Q00010001000200062Q0001003D00013Q0004D03Q003D000100304C0001000C000D2Q003A000200093Q00060F0002004500013Q0004D03Q004500012Q003A000200093Q00204401020002000E2Q009A0002000200012Q009D010200024Q00A6010200094Q003A000200053Q00060F0002004D00013Q0004D03Q004D00012Q003A000200053Q00204401020002000E2Q009A0002000200012Q009D010200024Q00A6010200054Q003A000200073Q00060F0002005500013Q0004D03Q005500012Q003A000200073Q00204401020002000E2Q009A0002000200012Q009D010200024Q00A6010200074Q003A000200013Q0020610102000200014Q00043Q000300302Q00040002000300302Q00040004000F00302Q0004000600074Q0002000400012Q00BA3Q00013Q00033Q00033Q0003073Q004B6579436F646503043Q00456E756D03053Q005370616365020C3Q00060F0001000300013Q0004D03Q000300012Q00BA3Q00013Q0020CB00023Q0001001257010300023Q0020CB0003000300010020CB00030003000300066D0102000B000100030004D03Q000B00012Q0071000200014Q00A601026Q00BA3Q00017Q00053Q0003073Q004B6579436F646503043Q00456E756D03053Q005370616365030D3Q00506C6174666F726D5374616E64010002153Q00200F01023Q000100122Q000300023Q00202Q00030003000100202Q00030003000300062Q00020014000100030004D03Q001400012Q007100026Q00A601026Q003A000200013Q00060F0002001400013Q0004D03Q001400012Q007100026Q004F000200016Q000200026Q000200026Q000200036Q00020001000200062Q0002001400013Q0004D03Q0014000100304C0002000400052Q00BA3Q00017Q00133Q0003083Q00476574537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503043Q004465616403083Q0046722Q6566612Q6C03073Q004A756D70696E67030D3Q00506C6174666F726D5374616E6401002Q01030D3Q004D6F7665446972656374696F6E03093Q004D61676E6974756465029A5Q99B93F2Q033Q00446F7403043Q00556E697403163Q00412Q73656D626C794C696E65617256656C6F6369747903093Q0057616C6B53702Q656403073Q00566563746F72332Q033Q006E6577029Q005B4Q003A7Q000658012Q0004000100010004D03Q000400012Q00BA3Q00014Q003A3Q00014Q009F012Q000100022Q003A000100024Q009F2Q010001000200060F3Q000C00013Q0004D03Q000C00010006582Q01000D000100010004D03Q000D00012Q00BA3Q00013Q0020440102000100012Q00FE00020002000200122Q000300023Q00202Q00030003000300202Q00030003000400062Q00020017000100030004D03Q001700012Q007100026Q00A6010200034Q00BA3Q00014Q003A000200044Q00F800038Q00020002000300202Q0004000100014Q00040002000200122Q000500023Q00202Q00050005000300202Q00050005000500062Q00040027000100050004D03Q00270001001257010500023Q0020CB0005000500030020CB0005000500060006C500040027000100050004D03Q002700012Q003F01056Q0071000500013Q00060F0005003500013Q0004D03Q0035000100060F0002003500013Q0004D03Q003500012Q003A000600053Q00060F0006003500013Q0004D03Q003500012Q003A000600033Q00065801060035000100010004D03Q003500012Q0071000600014Q00A6010600034Q00A6010300064Q003A000600033Q00060F0006005A00013Q0004D03Q005A000100065801020040000100010004D03Q004000012Q007100066Q0093000600036Q000600066Q000600063Q00302Q0001000700086Q00013Q00304C0001000700090020CB00060001000A0020CB00070006000B000E2C000C0050000100070004D03Q005000012Q003A000700063Q00209101080006000D4Q000A00066Q0008000A00024Q0007000700084Q00070006000700202Q00070007000E00202Q0008000100104Q00080007000800104Q000F000800044Q00570001001257010700113Q00200501070007001200122Q000800133Q00122Q000900133Q00122Q000A00136Q0007000A000200104Q000F000700060F0003005A00013Q0004D03Q005A00012Q00A6010300064Q00BA3Q00017Q001A3Q0003043Q0067616D65030A3Q004765745365727669636503133Q005669727475616C496E7075744D616E6167657203103Q0055736572496E70757453657276696365030A3Q0052756E5365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203043Q00456E756D03073Q004B6579436F646503043Q004C65667403053Q00526967687403013Q004103013Q0044030A3Q005465737453797374656D03093Q00412Q64546F2Q676C65030E3Q005475726E62696E64546F2Q676C6503053Q005469746C6503083Q005475726E62696E64030B3Q004465736372697074696F6E030A3Q00486F6C642041207C204403073Q0044656661756C74010003083Q0043612Q6C6261636B03123Q004261636B5475726E62696E64546F2Q676C6503123Q004261636B7761726473205475726E62696E6403143Q0041203D205269676874207C2044203D204C65667400653Q00127D012Q00013Q00206Q000200122Q000200038Q0002000200122Q000100013Q00202Q00010001000200122Q000300046Q00010003000200122Q000200013Q00202Q00020002000200128E010400054Q004B00020004000200122Q000300013Q00202Q00030003000200122Q000500066Q00030005000200202Q00030003000700122Q000400083Q00202Q00040004000900202Q00040004000A00122Q000500083Q0020CB0005000500090020D700050005000B00122Q000600083Q00202Q00060006000900202Q00060006000C00122Q000700083Q00202Q00070007000900202Q00070007000D4Q00088Q00098Q000A6Q0071000B6Q009D010C000D3Q000679000E3Q000100012Q0082016Q000679000F0001000100012Q0082012Q00033Q00067900100002000100062Q0082012Q00084Q0082017Q0082012Q00044Q0082012Q00094Q0082012Q00054Q0082012Q000C3Q00067900110003000100062Q0082012Q000A4Q0082017Q0082012Q00054Q0082012Q000B4Q0082012Q00044Q0082012Q000D4Q004F01125Q00202Q00120012000E00202Q00120012000F00122Q001400106Q00153Q000400302Q00150011001200302Q00150013001400302Q001500150016000679001600040001000D2Q0082012Q00114Q0082012Q000C4Q0082012Q00024Q0082012Q000F4Q0082012Q00084Q0082012Q000E4Q0082012Q00044Q0082012Q00014Q0082012Q00064Q0082012Q00094Q0082012Q00054Q0082012Q00074Q0082012Q00103Q0010320015001700164Q0012001500014Q00125Q00202Q00120012000E00202Q00120012000F00122Q001400186Q00153Q000400302Q00150011001900302Q00150013001A00302Q001500150016000679001600050001000D2Q0082012Q00104Q0082012Q000D4Q0082012Q00024Q0082012Q000F4Q0082012Q000A4Q0082012Q000E4Q0082012Q00054Q0082012Q00014Q0082012Q00064Q0082012Q000B4Q0082012Q00044Q0082012Q00074Q0082012Q00113Q00107A0015001700162Q00A20112001500012Q00BA3Q00013Q00063Q00023Q00030C3Q0053656E644B65794576656E7403043Q0067616D65031C3Q00060F0002000D00013Q0004D03Q000D00010006582Q01000D000100010004D03Q000D00012Q003A00035Q0020160103000300014Q000500016Q00068Q00075Q00122Q000800026Q0003000800014Q000300016Q000300023Q0006580102001A000100010004D03Q001A000100060F0001001A00013Q0004D03Q001A00012Q003A00035Q0020160103000300014Q00058Q00068Q00075Q00122Q000800026Q0003000800014Q00038Q000300024Q00DD000100024Q00BA3Q00017Q00053Q0003093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403063Q004865616C7468029Q00124Q003A7Q0020CB5Q0001000658012Q0006000100010004D03Q000600012Q007100016Q00DD000100023Q0020442Q013Q000200128E010300034Q009000010003000200069E00020010000100010004D03Q001000010020CB000200010004000E5E0005000F000100020004D03Q000F00012Q003F01026Q0071000200014Q00DD000200024Q00BA3Q00017Q00033Q00030C3Q0053656E644B65794576656E7403043Q0067616D65030A3Q00446973636F2Q6E65637400214Q003A7Q00060F3Q000C00013Q0004D03Q000C00012Q003A3Q00013Q0020645Q00014Q00028Q000300026Q00045Q00122Q000500028Q000500019Q009Q002Q003A3Q00033Q00060F3Q001800013Q0004D03Q001800012Q003A3Q00013Q0020645Q00014Q00028Q000300046Q00045Q00122Q000500028Q000500019Q006Q00034Q003A3Q00053Q00060F3Q002000013Q0004D03Q002000012Q003A3Q00053Q002044014Q00032Q009A3Q000200012Q009D017Q00A6012Q00054Q00BA3Q00017Q00033Q00030C3Q0053656E644B65794576656E7403043Q0067616D65030A3Q00446973636F2Q6E65637400214Q003A7Q00060F3Q000C00013Q0004D03Q000C00012Q003A3Q00013Q0020645Q00014Q00028Q000300026Q00045Q00122Q000500028Q000500019Q009Q002Q003A3Q00033Q00060F3Q001800013Q0004D03Q001800012Q003A3Q00013Q0020645Q00014Q00028Q000300046Q00045Q00122Q000500028Q000500019Q006Q00034Q003A3Q00053Q00060F3Q002000013Q0004D03Q002000012Q003A3Q00053Q002044014Q00032Q009A3Q000200012Q009D017Q00A6012Q00054Q00BA3Q00017Q00053Q0003073Q00546F2Q676C657303123Q004261636B5475726E62696E64546F2Q676C6503083Q0053657456616C756503093Q0048656172746265617403073Q00436F2Q6E65637401233Q00060F3Q002000013Q0004D03Q002000012Q003A00016Q002B0001000100010012572Q0100013Q00060F0001001000013Q0004D03Q001000010012572Q0100013Q0020CB00010001000200060F0001001000013Q0004D03Q001000010012572Q0100013Q0020CB0001000100020020442Q01000100032Q007100036Q00A22Q01000300012Q003A000100023Q0020CB0001000100040020442Q010001000500067900033Q000100092Q003A3Q00034Q003A3Q00044Q003A3Q00054Q003A3Q00064Q003A3Q00074Q003A3Q00084Q003A3Q00094Q003A3Q000A4Q003A3Q000B4Q00900001000300022Q00A62Q0100013Q0004D03Q002200012Q003A0001000C4Q002B0001000100012Q00BA3Q00013Q00013Q00013Q0003093Q0049734B6579446F776E00184Q003A8Q009F012Q00010002000658012Q0005000100010004D03Q000500012Q00BA3Q00014Q003A3Q00024Q00862Q0100036Q000200016Q000300043Q00202Q0003000300014Q000500056Q000300059Q0000026Q00018Q00026Q000100076Q000200066Q000300043Q00202Q0003000300014Q000500086Q000300059Q0000026Q00068Q00017Q00053Q0003073Q00546F2Q676C6573030E3Q005475726E62696E64546F2Q676C6503083Q0053657456616C756503093Q0048656172746265617403073Q00436F2Q6E65637401233Q00060F3Q002000013Q0004D03Q002000012Q003A00016Q002B0001000100010012572Q0100013Q00060F0001001000013Q0004D03Q001000010012572Q0100013Q0020CB00010001000200060F0001001000013Q0004D03Q001000010012572Q0100013Q0020CB0001000100020020442Q01000100032Q007100036Q00A22Q01000300012Q003A000100023Q0020CB0001000100040020442Q010001000500067900033Q000100092Q003A3Q00034Q003A3Q00044Q003A3Q00054Q003A3Q00064Q003A3Q00074Q003A3Q00084Q003A3Q00094Q003A3Q000A4Q003A3Q000B4Q00900001000300022Q00A62Q0100013Q0004D03Q002200012Q003A0001000C4Q002B0001000100012Q00BA3Q00013Q00013Q00013Q0003093Q0049734B6579446F776E00184Q003A8Q009F012Q00010002000658012Q0005000100010004D03Q000500012Q00BA3Q00014Q003A3Q00024Q00862Q0100036Q000200016Q000300043Q00202Q0003000300014Q000500056Q000300059Q0000026Q00018Q00026Q000100076Q000200066Q000300043Q00202Q0003000300014Q000500086Q000300059Q0000026Q00068Q00017Q00133Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403093Q00776F726B737061636503153Q0046696E6446697273744368696C644F66436C612Q73030D3Q00537061776E4C6F636174696F6E03063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103063Q00434672616D652Q033Q006E657703083Q00506F736974696F6E03073Q00566563746F7233028Q00026Q001440003B3Q00124Q00013Q00206Q000200122Q000200038Q0002000200202Q00013Q000400202Q00020001000500062Q00020009000100010004D03Q000900012Q00BA3Q00013Q00204401030002000600128E010500074Q00900003000500020006580103000F000100010004D03Q000F00012Q00BA3Q00013Q001257010400083Q00204401040004000900128E0106000A4Q009000040006000200065801040024000100010004D03Q002400010012570105000B3Q001246000600083Q00202Q00060006000C4Q000600076Q00053Q000700044Q00220001002044010A0009000D00128E010C000A4Q0090000A000C000200060F000A002200013Q0004D03Q002200012Q0082010400093Q0004D03Q002400010006480105001B000100020004D03Q001B000100060F0004003300013Q0004D03Q003300010012570105000E3Q00207700050005000F00202Q00060004001000122Q000700113Q00202Q00070007000F00122Q000800123Q00122Q000900133Q00122Q000A00126Q0007000A00024Q0006000600074Q00050002000200102Q0003000E000500044Q003A00010012570105000E3Q00200501050005000F00122Q000600123Q00122Q000700133Q00122Q000800126Q00050008000200102Q0003000E00052Q00BA3Q00017Q00", GetFEnv(), ...);
