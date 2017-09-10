-- Scheme interpreter in Lua
-- Copyright (C) 2017  Zaoqi

-- This program is free software: you can redistribute it and/or modify
-- it under the terms of the GNU Affero General Public License as published
-- by the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.

-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU Affero General Public License for more details.

-- You should have received a copy of the GNU Affero General Public License
-- along with this program.  If not, see <http://www.gnu.org/licenses/>.

local exports = {}

local function l_eval(exp)
	return assert(loadstring("return (" .. exp .. ")"))()
end

-- the global environment
local global_env = {}

-- The end-of-file object
local eof_obj = {}

-- the empty list object
local nil_obj = {}

-- the "undefined" object
local undef_obj = {}

-- booleans
local bool_true = {}
local bool_false = {}

local function is_char(obj)
   return type(obj) == "table" and obj[1] == "char"
end

local function is_nil(obj)
   return obj == nil_obj
end

local function is_number(obj)
   return type(obj) == "number"
end

local function is_pair(obj)
   return type(obj) == "table" and obj[1] == "pair"
end

local function is_continuation(obj)
   return type(obj) == "table" and obj[1] == "continuation"
end

local function is_primitive(obj)
   return type(obj) == "table" and obj[1] == "primitive"
end

local function is_procedure(obj)
   return type(obj) == "table" and obj[1] == "procedure"
end

local function is_symbol(obj)
   return type(obj) == "string"
end

local function is_string(obj)
   return type(obj) == "table" and obj[1] == "string"
end

local function is_true(obj)
   return obj ~= bool_false
end

local function is_vector(obj)
   return type(obj) == "table" and obj[1] == "vector"
end

local function make_string(str)
   strobj = {[1] = "string"}
   for i = 1, #str do
     strobj[i+1] = str:sub(i,i)
   end
   return strobj
end

local nodoc = make_string("No documentation available.")

local function make_char(c)
   return {[1] = "char", [2] = c}
end

local function make_pair(x, y)
   local pair = {[1] = "pair", [2] = nil_obj, [3] = nil_obj}

   if x then
      pair[2] = x
      if y then
	 pair[3] = y
      end
   end

   return pair
end

local function make_continuation(cont)
   return {[1] = "continuation", [2] = cont}
end

local function continuation_procedure(cont)
   if is_continuation(cont) then
      return cont[2]
   else
      error("Not a continuation")
   end
end

local function make_primitive(f, arity)
   return {[1] = "primitive", [2] = f, [3] = arity}
end

local function primitive_function(pri)
   if is_primitive(pri) then
      return pri[2]
   else
      error("Not a primitive")
   end
end

local function primitive_arity(pri)
   if is_primitive(pri) then
      return pri[3]
   else
      error("Not a primitive")
   end
end

local function make_procedure(args, env, body)
   return {[1] = "procedure", [2] = args, [3] = env, [4] = body, ["doc"] = ""}
end

local function procedure_args(proc)
   if is_procedure(proc) then
      return proc[2]
   else
      error("Not a procedure")
   end
end

local function procedure_env(proc)
   if is_procedure(proc) then
      return proc[3]
   else
      error("Not a procedure")
   end
end

local function procedure_body(proc)
   if is_procedure(proc) then
      return proc[4]
   else
      error("Not a procedure")
   end
end

local function add_primitive(name, f, arity)
   local pri = make_primitive(f, arity)
   global_env[name] = pri
end

--
-- Primitives
--

local function nullp(obj)
   if is_nil(obj) then
      return bool_true
   else
      return bool_false
   end
end

local function make_numerical_comparator(comp)
   return function (...)
	     local args = {...}

	     if #args < 2 then
		error("Comparison of less than two elements")
	     else
		local test = args[1]
		if not is_number(test) then
		   error("Numerical comparator applied to non-number")
		end
		for i = 2, #args do
		   local val = args[i]
		   if not is_number(val) then
		      error("Numerical comparator applied to non-number")
		   end
		   if not comp(test, val) then
		      return bool_false
		   end
		   test = val
		end

		return bool_true
	     end
	  end
end

local eq = make_numerical_comparator(function(a, b) return a == b end)
local lt = make_numerical_comparator(function(a, b) return a < b end)
local ge = make_numerical_comparator(function(a, b) return a > b end)
local le = make_numerical_comparator(function(a, b) return a <= b end)
local ge = make_numerical_comparator(function(a, b) return a >= b end)

local function add(...)
   local args = {...}

   if #args == 0 then
      return 0
   else
      local sum = 0
      for i = 1, #args do
	 if not is_number(args[i]) then
	    error("Adding non-number")
	 end
	 sum = sum + args[i]
      end
      return sum
   end
end

local function sub(...)
   local args = {...}

   if #args == 0 then
      error("No arguments to subtraction procedure")
   elseif #args == 1 then
      if not is_number(args[1]) then
	 error("Subtracting non-number")
      end
      return 0 - args[1]
   else
      local res = args[1]
      for i = 2, #args do
	 if not is_number(args[i]) then
	    error("Subtracting non-number")
	 end
	 res = res - args[i]
      end
      return res
   end
end

local function mul(...)
   local args = {...}

   if #args == 0 then
      return 1
   else
      local prod = 1
      for i = 1, #args do
	 if not is_number(args[i]) then
	    error("Multiplying non-number")
	 end
	 prod = prod * args[i]
      end
      return prod
   end
end

local function div(...)
   local args = {...}

   if #args == 0 then
      error("No arguments to division procedure")
   elseif #args == 1 then
      if not is_number(args[1]) then
	 error("Dividing non-number")
      end
      if args[1] == 0 then
	 error("Dividing by zero")
      end
      return 1 / args[1]
   else
      local res = args[1]
      for i = 2, #args do
	 if not is_number(args[i]) then
	    error("Dividing non-number")
	 end
	 if args[i] == 0 then
	    error("Dividing by zero")
	 end
	 res = res / args[i]
      end
      return res
   end
end

local function cons(x, y)
   return {[1] = "pair", [2] = x, [3] = y}
end

local function car(obj)
   if is_pair(obj) then
      return obj[2]
   else
      error("Not a pair passed to CAR")
   end
end

local function cdr(obj)
   if is_pair(obj) then
      return obj[3]
   else
      error("Not a pair passed to CDR")
   end
end

local function length(obj)
   local function l(p, n)
      local d = cdr(p)

      if is_nil(d) then
	 return n
      elseif is_pair(d) then
	 return l(d, n + 1)
      else
	 error("List expected")
      end
   end

   if is_nil(obj) then
      return 0
   elseif is_pair(obj) then
      return l(obj, 1)
   else
      error("List expected")
   end
end

local function doc(obj)
  if is_nil(obj) then
      return ""
  elseif is_procedure(obj) then
      return obj["doc"]
  else
      return ""
  end
end

local function cadr(obj)
   return car(cdr(obj))
end

local function cddr(obj)
   return cdr(cdr(obj))
end

local function caddr(obj)
   return car(cdr(cdr(obj)))
end

local function cdddr(obj)
	return cdr(cdr(cdr(obj)))
end

local function cadddr(obj)
   return car(cdr(cdr(cdr(obj))))
end

-- The reader
local function read(port)
   local last_char = false
   local port = port or io.input()

   local function is_space(c)
      return c == " " or c == "\n" or c == "\t" or c == "\r"
   end

   local function peek_char()
      if last_char == false then
	 last_char = port:read(1)
      end
      
      return last_char
   end

   local function get_char()
      local char = peek_char()

      -- set to false so the next time I ask for a char,
      -- it reads another one
      last_char = false

      return char
   end

   local function eat_space()
      local char

      char = peek_char()
      while is_space(char) do
	 get_char()
	 char = peek_char()
      end
   end

   local function inner_read()

      local function read_till_delimiter()
	 local char
	 local str = {}
	 
	 while true do
	    char = peek_char()
	    if is_space(char) or char == nil or char == "(" or char == ")"
	                      or char == "\"" or char == ";" then
	       return table.concat(str)
	    else
	       str[#str+1] = get_char()
	    end
	 end
      end

      local function read_list()
	 local pair = make_pair()
	 local p = pair

	 while true do
	    local exp = inner_read()
	    p[2] = exp
	    eat_space()
	    local c = peek_char()
	    if c == ")" then
	       get_char()
	       break
	    elseif c == "." then
	       get_char()
	       p[3] = inner_read()
	       eat_space()
	       c = peek_char()
	       if c == ")" then
		  get_char()
	       else
		  error("Unknown read syntax reading improper list: " .. c)
	       end
	       break
	    else
	       local p2 = make_pair()
	       p[3] = p2
	       p = p2
	    end
	 end

	 return pair
      end

      local function read_string()
	 local str = {[1] = "string"}

	 local char = get_char()
	 while char ~= "\"" do
	    str[#str+1] = char
	    char = get_char()
	 end

	 return str
      end

      local function read_symbol(first)
	 local rest = read_till_delimiter()

	 local str = first .. rest
	 if str:match("[%d%+%-%.%a%$%%%*%?%^!&/:<=>_~@]+") then
	    return str
	 else
	    error("Unknown read syntax: " .. str)
	 end
      end

      local function read_vector()
	 local char
	 local vec = {[1] = "vector"}
	 
	 eat_space()
	 char = peek_char()
	 while char ~= ")" do
	    local exp = inner_read()
	    if exp == eof_obj then
	       error("Unterminated vector")
	    else
	       vec[#vec+1] = exp
	    end
	    eat_space()
	    char = peek_char()
	 end
	 get_char()

	 return vec
      end

      local char = get_char()

      -- discarding white spaces and comments
      while is_space(char) or char == ";" do
	 while is_space(char) do
	    char = get_char()
	 end
	 
	 if char == ";" then
	    while char ~= "\n" do
	       char = get_char()
	    end
	 end
      end

      -- reading
      if char == nil then
	 return eof_obj
      elseif char == "'" or char == "`" then
	 local exp = inner_read()
	 local p1 = make_pair()
	 local p2 = make_pair()
	 if char == "'" then
	    p1[2] = "quote"
	 else
	    p1[2] = "quasiquote"
	 end
	 p1[3] = p2
	 p2[2] = exp
	 p2[3] = nil_obj
	 return p1
      elseif char == "," then
	 local p1 = make_pair()
	 local p2 = make_pair()
	 p1[2] = "unquote"
	 char = peek_char()
	 if char == "@" then
	    get_char()
	    p1[2] = "unquote-splicing"
	 end
	 local exp = inner_read()
	 p1[3] = p2
	 p2[2] = exp
	 p2[3] = nil_obj
	 return p1
      elseif char == "#" then
	 local c = peek_char()
	 if c == "(" then
	    get_char()
	    return read_vector()
	 elseif c == "\\" then
	    -- characters
	    get_char()
	    c = read_till_delimiter()
	    if c == "space" then
	       return make_char(" ")
	    elseif c == "newline" then
	       return make_char("\n")
	    elseif c:len() == 1 then
	       return make_char(c)
	    else
	       error("Unknown character: " .. c)
	    end
	 else
	    local str = read_till_delimiter()
	    if str == "f" then
	       return bool_false
	    elseif str == "t" then
	       return bool_true
	    else
	       error("Unknown read syntax: #" .. c)
	    end
	 end
      elseif char == "(" then
	 local c
	 eat_space()
	 c = peek_char()
	 if c == ")" then
	    get_char()
	    return nil_obj
	 else
	    return read_list()
	 end
      elseif char == "\"" then
	 return read_string()
      elseif char:match("%d") then
	 local rest = read_till_delimiter()
	 local str = char .. rest
	 local num = tonumber(str)
	 if num then
	    return num
	 else
	    error("Unknown reader syntax: " .. str)
	 end
      elseif char:match("[%a%$%%%*%?%^!&/:<=>_~]") then
	 return read_symbol(char)
      elseif char == "+" or char == "-" then
	 local rest = read_till_delimiter()
	 if rest == "" then
	    return char
	 else
	    local num = tonumber(rest)
	    if num then
	       if char == "+" then
		  return num
	       else
		  return -num
	       end
	    else
	       error("Unknown read syntax: " .. char .. rest)
	    end
	 end
      elseif char == "." then
	 local rest = read_till_delimiter()
	 if rest == ".." then
	    return "..."
	 else
	    error("Unknown read syntax: ." .. rest)
	 end
      else
	 error("Unknown read syntax: "  .. char)
      end
   end

   return inner_read()
end

local function string2l_string(exp)
	if is_string(exp) then
		return table.concat(exp, "", 2)
	else
		error("Not a string")
	end
end

local function write(exp, port)

   local port = port or io.output()

   local function l_write(obj)
      return port:write(obj)
   end

   if exp == eof_obj then
      l_write("#<eof>")
   elseif exp == nil_obj then
      l_write("()")
   elseif exp == undef_obj then
      l_write("#<undefined>")
   elseif exp == bool_true then
      l_write("#t")
   elseif exp == bool_false then
      l_write("#f")
   elseif type(exp) == "string" or type(exp) == "number" then
      l_write(exp)
   elseif is_char(exp) then
      if exp[2] == " " then
	 l_write("#\\space")
      elseif exp[2] == "\n" then
	 l_write("#\\newline")
      else
	 l_write("#\\")
	 l_write(exp[2])
      end
   elseif is_pair(exp) then
      l_write("(")
      local first = true
      while true do
	 if not first then l_write(" ") end
	 first = false
	 write(exp[2], port)
	 if is_pair(exp[3]) then
	    exp = exp[3]
	 elseif exp[3] == nil_obj then
	    break
	 else
	    l_write(" . ")
	    write(exp[3], port)
	    break
	 end
      end
      l_write(")")
   elseif is_procedure(exp) then
      l_write("#<procedure>")
   elseif is_string(exp) then
      l_write("\""..string2l_string(exp).."\"")
   elseif is_vector(exp) then
      l_write("#(")
      for i = 2, #exp do
	 if i ~= 2 then
	    l_write(" ")
	 end
	 write(exp[i], port)
      end
      l_write(")")
   else
      error("Unknown Scheme type to write")
   end

   return undef_obj
end

local function newline(port)
   local port = port or io.output()

   port:write("\r\n")

   return undef_obj
end

local function table2list(t)
	local r = nil_obj
	for k, v in pairs(t) do
		r = cons(cons(l2sv(k, true), l2sv(v, false)), r)
	end
end

local function list2table(v)
	if is_nil(v) then
		return {}
	end
	local xs = list2table(cdr(v))
	local p = car(v)
	xs[car(p)] = s2lv(cdr(p))
	return xs
end

local s2lv = nil

local function l2sv(v, s)
	local t = type(v)
	if t == "number" then
		return v
	elseif t == "string" then
		if s then
			return v
		else
			return make_string(v)
		end
	elseif t == "nil" then
		return nil_obj
	elseif t == "boolean" then
		if t then
			return bool_true
		else
			return bool_false
		end
	elseif t == "table" then
		if l_is_list(v) then
			return l2list(v)
		else
			return table2list(v)
		end
	elseif t == "function" then
		return make_primitive(function(...)
				local a = {}
				for i, v in ipairs{...} do
					a[i] = s2lv(v)
				end
				return l2sv(v(unpack(a)))
			end
		, -1)
	else
		error("Unknown Lua type")
	end
end

local function is_table(v)
	if is_nil(v) then
		return true
	end
	if not is_pair(v) then
		return false
	end
	local p = car(v)
	return (is_pair(p) and is_symbol(car(p)) and is_table(cdr(p)))
end

local function is_list(v)
	return (is_nil(v) or (is_pair(v) and is_list(cdr(v))))
end

local function l_is_list(v)
	for i, v in pairs(v) do
		if type(i) ~= "number" then
			return false
		end
	end
	return true
end

local function l2list(v)
	local r = nil_obj
	for i = 1, #v do
		r = cons(l2sv(v[i]), r)
	end
	return r
end

local function list2l(rv)
	local r = {}
	local v = rv
	while not is_nil(v) do
		r[#r+1] = car(s2lv(v))
		v = cdr(v)
	end
	return r
end

s2lv = function(v)
	if is_primitive(v) then
		return primitive_function(v)
	elseif v == bool_true then
		return true
	elseif v == bool_false then
		return false
	elseif is_procedure(v) then
		return (function (...)
				local a = nil_obj
				local xs = {...}
				for i = #xs, 1, -1 do
					a = cons(l2sv(x), a)
				end
				return eval(cons(v, a))
			end)
	elseif is_nil(v) then
		return nil
	elseif is_table(v) then
		return list2table(v)
	elseif is_list(v) then
		return list2l(v)
	elseif is_number(v) then
		return v
	elseif is_string(v) then
		return string2l_string(v)
	else
		error("Unknown Scheme type")
	end
end

local function apply_lua(f, ...)
	local a = {}
	for i, v in ipairs{...} do
		a[i] = s2lv(v)
	end
	return (l_eval(string2l_string(f)))(unpack(a))
end

local function eval_lua(exp)
	return l2sv(l_eval(string2l_string(exp)))
end

local function eval(exp, env)

   local env = env or global_env

   -- looks for the value of a binding in the environment.
   -- environments are tables chained by their values at [1], since all
   -- bindings are stored with string keys
   local function lookup(exp, env)
      local val = env[exp]
      if val then
	 return val
      else
	 if env[1] then
	    return lookup(exp, env[1])
	 else
	    error("No such binding: " .. exp)
	 end
      end
   end

   local function update(var, val, env)
      if env[var] then
	 env[var] = val
      elseif env[1] then
	 return update(var, val, env[1])
      else
	 error("Assignment to unitialised variable")
      end
   end

   local function evaluate(exp, env, cont)

      local function evaluate_begin(body, env, cont)
	 if is_nil(body) then
	    return cont(undef_obj)
	 else
	    local exp = car(body)
	    if is_nil(cdr(body)) then
	       return evaluate(exp, env, cont)
	    else
	       return evaluate(exp, env, function (v)
					    return evaluate_begin(cdr(body),
								  env,
								  cont)
					 end)
	    end
	 end
      end

      -- this is let, not let*, so the bindings are evaluated in the old env,
      -- which we must carry along
      local function evaluate_let(bindings, new_env, env, body, cont)
	 if is_nil(bindings) then
	    return evaluate_begin(body, new_env, cont)
	 else
	    local binding = car(bindings)
	    local var = car(binding)
	    local exp = cadr(binding)
	    if not is_symbol(var) then
	       error("Not binding to symbol")
	    end

	    return evaluate(exp, env, function(v)
					 new_env[var] = v
					 return evaluate_let(cdr(bindings),
							     new_env,
							     env,
							     body,
							     cont)
				      end)
	 end
      end

      local function evaluate_apply(args, vals, new_env, env, body, cont)
	 if is_nil(args) then
	    return evaluate_begin(body, new_env, cont)
	 else
	    local arg = car(args)
	    local exp = car(vals)
	    if not is_symbol(arg) then
	       error("Not binding to symbol")
	    end

	    return evaluate(exp, env, function(v)
					 new_env[arg] = v
					 return evaluate_apply(cdr(args),
							       cdr(vals),
							       new_env,
							       env,
							       body,
							       cont)
				      end)
	 end
      end

      local function evaluate_primitive(f, args, vals, env, cont)
	 if is_nil(vals) then
	    return cont(f(unpack(args)))
	 else
	    local val = car(vals)
	    return evaluate(val, env, function(v)
					 args[#args+1] = v
					 return evaluate_primitive(f, args,
								   cdr(vals),
								   env, cont)
				      end)
	 end
      end

      if not is_pair(exp) then
	 if is_symbol(exp) then
	    local val = lookup(exp, env)
	    return cont(val)
	 else
	    return cont(exp)
	 end
      else
	 local op = car(exp)
	 if op == "quote" then
	    return cont(cadr(exp))
	 elseif op == "begin" then
	    return evaluate_begin(cdr(exp), env, cont)
	 elseif op == "call/cc" then
	    return evaluate(cadr(exp), env, function(v)
					       local args = procedure_args(v)
					       local fenv = procedure_env(v)
					       local body = procedure_body(v)
					       local proc = make_continuation(cont)
					       local vals = cons(proc, nil_obj)
					       local new_env = {[1] = fenv}
					       return evaluate_apply(args, vals,
								     new_env, env,
								     body, cont)
					    end)
	 elseif op == "define" then
	    local var = cadr(exp)
            local docstring = caddr(exp)
            if is_string(docstring) and (not is_nil(cdddr(exp))) then
               exp = cdr(exp)
            else
               docstring = nodoc
            end
	    if is_pair(var) then
	       local fname = car(var)
               local args = cdr(var)
               local docstring = nodoc
               if not is_nil(args) then
                 local mdoc = cadr(var)
                 if is_string(mdoc) then
                   docstring = mdoc
                   args = cddr(var)
                 end
               end
	       local body = cddr(exp)
	       local proc = make_procedure(args, env, body)
               proc["doc"] = docstring
	       if not is_symbol(fname) then
		  error("Procedure name must be a symbol!")
	       end

	       env[fname] = proc
	       return cont(undef_obj)
	    else
	       if not is_symbol(var) then
		  error("Assignment to non-symbol!")
	       end
	       return evaluate(caddr(exp), env, function(v)
	           if type(v) == "table" then
                 v["doc"] = docstring
               end
               env[var] = v
               return cont(undef_obj)
               end)
	    end
	 elseif op == "if" then
	    return evaluate(cadr(exp),
			    env,
			    function(v)
			       if is_true(v) then
				  return evaluate(caddr(exp), env, cont)
			       else
				  return evaluate(cadddr(exp), env, cont)
			       end
			    end)
	 elseif op == "lambda" then
	    local args = cadr(exp)
	    local body = cddr(exp)

	    return cont(make_procedure(args, env, body))
	 elseif op == "let" then
	    local body = cddr(exp)
	    local bindings = cadr(exp)

	    if is_nil(bindings) then
	       return evaluate_begin(body, env, cont)
	    elseif is_pair(bindings) then
	       local new_env = {[1] = env}

	       return evaluate_let(bindings, new_env, env, body, cont)
	    else
	       error("Invalid bindings in let form")
	    end
	 elseif op == "set!" then
	    local var = cadr(exp)
	    if not is_symbol(var) then
	       error("Assignment to non-symbol!")
	    end

	    return evaluate(caddr(exp), env, function(v)
						update(var, v, env)
						return cont(undef_obj)
					     end)
	 else
	    -- function application
	    return evaluate(op, env, function(v)
					local vals = cdr(exp)
					if is_continuation(v) then
					   local k = continuation_procedure(v)

					   return evaluate(car(vals),
							   env,
							   function(v)
							      return k(v)
							   end)
					elseif is_procedure(v) then
					   local args = procedure_args(v)
					   local fenv = procedure_env(v)
					   local body = procedure_body(v)
					   local new_env = {[1] = fenv}

					   return evaluate_apply(args, vals, new_env,
								 env, body, cont)
					elseif is_primitive(v) then
					   local num_vals = length(vals)
					   local f = primitive_function(v)
					   local a = primitive_arity(v)
					   if a < 0 or a == num_vals then
					      return evaluate_primitive(f, {}, vals,
									env, cont)
					   else
					      error("Incorrect arity of primitive")
					   end
					else
					   error("Trying to apply non-procedure")
					end
				     end)
	 end
      end
   end

   return evaluate(exp, env, function(v) return v end)
end

add_primitive("=", eq, -1)
add_primitive("<", lt, -1)
add_primitive(">", gt, -1)
add_primitive("<=", le, -1)
add_primitive(">=", ge, -1)
add_primitive("+", add, -1)
add_primitive("-", sub, -1)
add_primitive("*", mul, -1)
add_primitive("/", div, -1)
add_primitive("car", car, 1)
add_primitive("cdr", cdr, 1)
add_primitive("cons", cons, 2)
add_primitive("null?", nullp, 1)
add_primitive("length", length, 1)
add_primitive("write", write, 1)
add_primitive("newline", newline, 0)
add_primitive("doc", doc, 1)
add_primitive("eval-lua", eval_lua, 1)
add_primitive("apply-lua", apply_lua, -1)
--
-- Module interface
--

-- loads files
function exports.load(fname)
   local status, exp

   if (not fname) or fname == "" then
      return
   end

   local port, err = io.open(fname, "rb")
   if not port then
      io.write("Error opening Scheme file: " .. err .. "\r\n")
      return
   end

   status, exp = xpcall(function() return read(port) end, debug.traceback)
   if not status then
      io.write("Error: " .. exp .. "\r\n")
      port:close()
      return
   end

   while exp ~= eof_obj do

      status, exp = xpcall(function() return eval(exp) end, debug.traceback)
      if not status then
	 io.write("Error: " .. exp .. "\r\n")
	 port:close()
	 return
      end

      status, exp = xpcall(function() return read(port) end, debug.traceback)
      if not status then
	 io.write("Error: " .. exp .. "\r\n")
	 port:close()
	 return
      end

   end

   port:close()
end

-- the REPL
function exports.repl()
   local function toplevel()
      local status, exp
      io.write("scheme> ")

      status, exp = xpcall(read, debug.traceback)
      if not status then
	 io.write("Error: " .. exp .. "\r\n")
	 return toplevel()
      end

      if exp ~= eof_obj then

	 status, exp = xpcall(function() return eval(exp) end, debug.traceback)
	 if not status then
	    io.write("Error: " .. exp .. "\r\n")
	    return toplevel()
	 end

	 write(exp)
	 io.write("\r\n")
	 return toplevel()
      else
	 return true
      end
   end
   return toplevel()
end

return exports
