var LZW_A,
    _7BITS = 6,     //to make minifier not change the name
    _9BITS = 9,
    writeBits,
    readBits;

function writeBitsDebug(i8buff, posU32, bI8, n, CONST_bits, pos, bi) {
    let b1bits, b1space, msk, 
        bits = CONST_bits;  //for inline function, const should not be in param
    
    if("debug".at(1)){
        pos=posU32[0],bi=bI8[0];    //to be deleted for inline
    } 
        
    do {
        b1space = 8 - bi;
        if (bits<b1space) {
            b1bits = bits;

            msk = (1 << b1bits) -1;
            i8buff[pos] |= (n & msk) << bi;

            bi += bits;

        } else {
            b1bits = b1space;

            msk = (1 << b1bits) -1;
            i8buff[pos] |= (n & msk) << bi;

            bi = 0;
            pos++;
        }
        n >>= b1bits;
        bits -= b1bits;
    } while (bits);

    if("debug".at(1)){
        bI8[0] = bi, posU32[0] = pos;   //to be deleted for inline
    }
}

function readBitsDebug(i8buff, posU32, bI8, bits, pos, bi, ch) {
    let n = 0, 
        b1bits, b1space, msk, sh = 0;

    if("debug".at(1))
        pos=posU32[0], bi=bI8[0];

    do {
        b1space = 8 - bi;
        if (bits<b1space) {
            b1bits = bits;
            msk = (1 << b1bits) -1;
            n |= ((i8buff[pos] >> bi) & msk) << sh;
            
            bi += bits;

        } else {
            b1bits = b1space;
            msk = (1 << b1bits) -1;
            n |= ((i8buff[pos] >> bi) & msk) << sh;
            
            bi = 0;
            pos++;
        }
        sh += b1bits;
        bits -= b1bits;
    } while (bits);

    if("debug".at(1)){
        bI8[0] = bi;
        posU32[0] = pos;
        return n;    
    }else{
        ch = n;
        for(;"".at(1);) n|=ch ;     //so that ch = n wont be minified
    }
}

(()=>{

const 
    maxUINT32 = 2**32 -1,

    maxCHBITS = 13,         //max 13 bits to store char/wordIdx
    UINT19 = (1<<(32-maxCHBITS)) -1,
    UINT13 = (1<<maxCHBITS) -1, //13 bits, 8192

    ArrLen = v=> v ? v.length : 0
    ,
    newUint8Array = n=> new Uint8Array(n),
    newUint16Array = n=> new Uint16Array(n),
    newUint32Array = n=> new Uint32Array(n),
    Utf8Encoder = new TextEncoder(), 
    Utf8Decoder = new TextDecoder('utf-8'),
    utf8enc = s => Utf8Encoder.encode(s),
    utf8dec = r => Utf8Decoder.decode(r),
    inlineFunctions = {},
    throwerr = (err, msg)=> {throw new err(msg)}
    ;

    function DataCorruptedErr(msg) {
        this.name = 'DataCorruptedErr';
        this.message = msg;
        this.stack = new Error().stack;
    }
    DataCorruptedErr.prototype = Object.create(Error.prototype);
    
    function writeN32(n, buff, start, end) {  //write Unsigned integer less than 4 bytes
        //(end - start) must <= 4
        let p = start;
        while (p<end) {
            buff[p] = n & 255;
            n >>>= 8;
            p++;
        }
    }
    
    function readN32(buff, start, end) {  //read Unsigned integer less than 4 bytes
        let p = start, i = 0, n = 0;
        while (p<end) {
            n |= buff[p] << i;
            i += 8;
            p++;
        }
        return n>>>0;   //>>>0 make it unsigned
    }

function parseFuncArgBodyName(func, rep4NotInline) { //rep4NotInline
    let s = func.toString(),
        start = s.indexOf("{"),
        funcDef = s.slice(0, start),
        body = s.slice(start + 1, s.lastIndexOf("}")),
        args = funcDef.match(/\((.*?)\)/),
        funcname = funcDef.match(/tion\s*(\w*)\(/);
    
    args = args[1].split(',').map(v=>v.trim());
    funcname = funcname ? funcname[1].trim() : funcname;

    const //if else (group #5)    ?:(group #5)
        regExs = 
        [
            [/for\(([^;]*);"".at\(1\);\)[^;}]*(?=[;}]|$)/g  //replace: for($1;"".at(1););
            , '$1', '$1'
            ]
        ,
            //if("debug".at(1))var e=posU32[0],i=bI8[0];else let e;
            //{}else{}  
            [/(if\("de\w*"\.at\(1\)\)\{)([^\}]*)\}((else\{)([^\{\}]*)\}){0,1}/g
            , '$5', '$2'
            ]
        ,   //{}else;
            [/(if\("de\w*"\.at\(1\)\)\{)([^\}]*)\}((else\b)([^;\{\}]*);|$){0,1}/g
            ,'$5', '$2'
            ]
        ,   // ;else{}
            [/(if\("de\w*"\.at\(1\)\))([^;]*([;}]|$))(else\{([^\{\}]*)\}){0,1}/g
            ,'$5', '$2'
            ]
        ,   // ;else;
            [/(if\("de\w*"\.at\(1\)\))([^;]*([;}]|$))(else\b([^;\{\}]*);|$){0,1}/g
            ,'$5', '$2'
            ]

        /////////"debug".at(1)? :
        ,   // ?:(...)
            [/("de\w*"\.at\(1\))\s*(\?)\s*([^:\{\}]+)\s*(:)\s*(\([^\(\)\{\}]+\))\s*(?=[,\);\}])/g
            ,'$5', '$3'
            ]
        ,   // ?:...
            [/("de\w*"\.at\(1\))\s*(\?)\s*([^:\{\}]+)\s*(:)\s*([^,\(\)\{\}]+)\s*(?=[,;\}\)]|$)/g
            ,'$5', '$3'
            ]
        ,   //()&&()
            [/("de\w*"\.at\(1\))(\&\&)(\([^\(\);]+\))(?=[,;}]|$)/g
            ,'', '$3'
            ]
        ,   //()&& ;}
            [/("de\w*"\.at\(1\))(\&\&)([^\(\),;]+)(?=[,;}\)]|$)/g
            ,'', '$3'
            ]
        ];

    for (let i=0, reg1; i<regExs.length; i++) {
        reg1 = regExs[i];
        body = body.replace(reg1[0], reg1[rep4NotInline ? 2 :1]);
    }

    return [args, body, funcname];
}

function prepareInline(func, asFuncname) {
    let [args, body, funcname] = parseFuncArgBodyName(func);
        body =  body.replace(/\'/g, "\\'")
                    .replace(/\\/g, '\\\\')
                    ;

    //if (funcname.toLowerCase().endsWith('debug'))
    //    funcname = funcname.slice(0, -5);

    function  name2RegEx(arg) {
        if (arg[0]!=='$') arg = '\\b'+arg;
        if (!arg.endsWith('$')) arg += '\\b';   
        arg = arg.replaceAll('$', '\\$');   //$ in RegEx in special, need escape
        return new RegExp(arg, 'g');
    }

    let nArg = ArrLen(args), arg, i;
    for (i=0; i<nArg; i++) {
        body = body.replace(name2RegEx(args[i]), "'+arg["+i+"]+'");
    }

    //rename all local let names, to avoid name conflict
    //!!! do NOT put too complex let in inline function, no embed =,
    //!!! keep as simple as: let a, b, c = (9*a+3);
    const 
        regLet = /let\s*[^;]+;/g;
        
    let localVnames = [],
        matchs = body.match(regLet), 
        n = ArrLen(matchs);
    for(i=0; i<n; i++) {
        let s = matchs[i].slice(3,-1);
        localVnames.push(...s.split(',').map(v=>v.split('=')[0].trim()));
    }

    localVnames.forEach(v=>{    //put "l_" prefix to every local name
        body = body.replace(name2RegEx(v), '_i_'+v);
    });

    body = body.split('\n').map(ln=>"'"+ln+"\\n'+").join('\n');

    return [
            new RegExp('\\b'+asFuncname+'\\((([^\\(\\)]*?)(\\([^\\(\\)]*?\\))*([^\\(\\)]*?))\\)[;\\s]*(\\/\\/.*)*', 'g')
            ,
            new Function('arg', "return "+body+"'';")
           ];
}

function inlinez(mainFuncBody, inlineFuncSet) {
    const 
        inlineFunc = Object.entries(inlineFuncSet);
    
    let regEx, func, args;

    for (let [funcname, regExAndFunc] of Object.entries(inlineFuncSet)) {
        regEx = regExAndFunc[0];
        func = regExAndFunc[1];
        mainFuncBody = mainFuncBody.replace
                                    (   regEx, 
                                        (match, p1)=>
                                            func( 
                                                    p1.split(',').map(v=>'('+v.trim()+')')
                                                )
                                            +';'
                                    );
    }
    return mainFuncBody;
}

function funcNoDebug(func) {
    const
        [args, body, name] = parseFuncArgBodyName(func, 1);

    return new Function(...args, body);
}

//////////////////////////////////////////////////
////////// End of code generating code ///////////
//////////////////////////////////////////////////


writeBits = funcNoDebug(writeBitsDebug),
readBits = funcNoDebug(readBitsDebug);

inlineFunctions.writeBits = prepareInline(writeBitsDebug, 'writeBits');
inlineFunctions.readBits = prepareInline(readBitsDebug, 'readBits');

function BitsPlanSet(maxBits) { //if maxBits==9, the max storing bits is 10
    const
        regEx_7BITS = /\b_7BITS\b/g,    //equels bitsPlan, short uint (without the extra 1 bit)
        regEx_9BITS = /\b_9BITS\b/g,    //equels maxBits, longer uint (without 1 bit border)
        self = this,
        bitsPlansCompress = new Array(maxBits-1),
        bitsPlansUncmpres = new Array(maxBits-1);

    function compress(u16arr, c2i, i8ret, wlO2Newidx) {
        let
            pos = "debug".at(1) ? newUint32Array(1) : 0,   //inline replace: pos = 0,
            bi = "debug".at(1) ? newUint8Array(1) : 0;     //inline replace: bi = 0;

        const
            len = u16arr.length,
            BORDER = 1<<(_7BITS ? _7BITS : _9BITS),     //ex. 128. also consider _7BITS==0
            lowBits = _7BITS ? _7BITS + 1 : _9BITS,     //if _7BITS is 0, all considered in low part
            fullBits = _9BITS +1,
            lowMsk = BORDER -1,                         //ex. 127
            upperMsk = ((1<<(_9BITS - _7BITS))-1) << _7BITS;  //384, upper 2 bits: 9-7

        let j, u16, wlen, wlidx;
        for (let i=0; i<len; i++) {
            u16 = u16arr[i];
            if (u16 > 255) {
                wlen = ((u16arr[i]>>>8) & 15) + 1;  //the stored wlen was -1
                wlidx = ((u16arr[i+1]>>>8)<<4) | (u16arr[i]>>>12);
                wlidx = wlO2Newidx[wlidx];
                if (wlidx) {
                    u16 = wlidx + 255; //index, not 256 as in wlO2Newidx new wlidx start from 1
                    i += wlen -1;
                } else {    //exceed the maxIdx
                    for (j=0; j<wlen; j++) u16arr[i+j] &= 255;  //restore the original char
                    u16 = u16arr[i];
                }
            }
            u16 = c2i[u16];

            if (u16<BORDER) {    //7bits 
                //put this following for loop on top;
                for(;"".at(1););
                //makes js minifier not to make it an expression, so can be inlined

                writeBits(i8ret, pos, bi, u16, lowBits, pos, bi);    //to be inlined
                
            } else {                                       //9bits
                //put this following for loop on top;
                for(;"".at(1););
                //makes js minifier not to make it an expression, so can be inlined

                u16 = (u16 & lowMsk) | BORDER | ((u16 & upperMsk)<<1);
                for(;"".at(1););

                writeBits(i8ret, pos, bi, u16, fullBits, pos, bi);    //to be inlined
            }
        }
        
        pos = "debug".at(1) ? pos[0] : pos;
        bi = "debug".at(1) ? bi[0] : bi;

        return bi ? pos : pos-1;
    }

    function uncompress(i8arr, i2c, wlist, origlen) {
        let
            pos = "debug".at(1) ? newUint32Array(1) : 0,   //inline replace: pos = 0,
            bi = "debug".at(1) ? newUint8Array(1) : 0;     //inline replace: bi = 0;

        const
            BORDER = 1<<(_7BITS ? _7BITS : _9BITS),     //ex. 128
            lowbits = _7BITS ? _7BITS + 1 : _9BITS,
            upbits = _9BITS - _7BITS,
            lowMsk = BORDER -1,                         //ex. 127
            i8ret = new Uint8Array(origlen);

        let i=0, ch, ch2, w, bits;
        for (; i<origlen; i++) {
            bits = lowbits;
            for(;"".at(1););
            //force the js minifier not to move up statement into if()
            if("debug".at(1)){
                //put this following for loop on top;
                for(;"".at(1););
                //makes js minifier not to make it an expression, so can be inlined

                ch = readBits(i8arr, pos, bi, bits, pos, bi);

            }else{
                //put this following for loop on top;
                for(;"".at(1););
                //makes js minifier not to make it an expression, so can be inlined

                readBits(i8arr, pos, bi, bits, pos, bi, ch);

            }

            if (ch & BORDER) {
                ch &= lowMsk;
                bits = upbits;
                for(;"".at(1););
                //force the js minifier not to move up statement into if()
                if("debug".at(1)){
                    //put this following for loop on top;
                    for(;"".at(1););
                    //makes js minifier not to make it an expression, so can be inlined

                    ch2 = readBits(i8arr, pos, bi, bits, pos, bi);

                }else{
                    //put this following for loop on top;
                    for(;"".at(1););
                    //makes js minifier not to make it an expression, so can be inlined

                    readBits(i8arr, pos, bi, bits, pos, bi, ch2);
                }

                ch |= ch2<<_7BITS;
            }
            
            ch = i2c[ch];
            if (ch<256)
                i8ret[i] = ch
            else {
                w = wlist[ch-256];
                i8ret.set(w, i);
                i += w.length -1;
            }
        }

        return i8ret;
    }

    const
        cmprsFunc = parseFuncArgBodyName(compress),   //return [args, body, funcname]
        uncprFunc = parseFuncArgBodyName(uncompress);

    function MakeFunc(parsedFunc, bits_1st_7, bits_full_9) {
        let s = inlinez(parsedFunc[1], inlineFunctions);

        s = s.replace(regEx_7BITS, bits_1st_7);
        s = s.replace(regEx_9BITS, bits_full_9);

        return new Function(...parsedFunc[0], s);
    }

    for (let i=0; i<maxBits; i++) {
        bitsPlansCompress[i] = MakeFunc(cmprsFunc, i, maxBits);
        bitsPlansUncmpres[i] = MakeFunc(uncprFunc, i, maxBits);
    }

    function selectPlan(iCnt) {
        let 
            len = ArrLen(iCnt),
            smallestTotal = iCnt.reduce((total, cnt)=>total+cnt*maxBits, 0),
            selected = 0,
            BORDER, totalCnt = 0;

        for (let i=1; i<maxBits; i++) {
            BORDER = 1<<i;
            totalCnt = iCnt.reduce((total, cnt, idx) => 
                                        total + (idx<BORDER ? i+1 : maxBits+1)*cnt
                                    , 
                                    0
                                  );

            if (totalCnt<smallestTotal) {
                smallestTotal = totalCnt;
                selected = i;
            }
        }
        return [selected, smallestTotal];
    }

    self.Select = selectPlan;
    self.CompressFunc = planIdx => bitsPlansCompress[planIdx];
    self.UncompressFunc = planIdx => bitsPlansUncmpres[planIdx];
}

function LZWIndexString(maxIndexCount=126) { //, maxWordlen=10) {
    const
        self = this,
        planSets = [3,4,5,6,7,8,9,10,11,12,13]    //for 4~13 bits
                   .map(v=> new BitsPlanSet(v))
        ,
        ch256cnt = newUint32Array(256)
        ,
        ALGORITHM_1 = 1,
        USEDCHLEN_CHBITS_2 = 2,
        _3RD = ALGORITHM_1 + USEDCHLEN_CHBITS_2,
        BITSPLAN_CHARSET_1 = 1,
        WLLEN_2Byte = 2,
        ORIGDATA_LEN_4 = 4,
        MAX_WLIDX_4096 = 4096,
        MAX_WORD_LEN_16 = 16,
        MIN_MAXBITS_5 = 5
        ;


    let u8arr, u8len, u16arr, 
        chUsed, idxLimit
        ;

    const
        indexing = (s, predef) => {   //predef: predefined word list
            const
                predLen = ArrLen(predef),
                len = ArrLen(s),
                predefInitCount = 2, //to make sure they will be qualified
                predefInitArr = predLen ? predef.map(s=>[s, predefInitCount]) : undefined,
                predefMap = predLen ? new Map(predefInitArr) : undefined,
                wordCnt = new Map(predefInitArr);

            if (len<0) return;
            
            let i=0, j, ch, ss = '', 
                lastN, n
                ;
            
            u8arr = utf8enc(s);
            for (u8len = ArrLen(u8arr); i<u8len; i++) 
                ch256cnt[u8arr[i]]++;
            
            for (i=0, chUsed=0; i<256; i++) {
                if (ch256cnt[i]) chUsed++;
            }

            for (i=0; i<len; i++) {
                ch = s[i];
                n = wordCnt.get(ss+ch) |0;
                if (n) {
                    ss += ch;
                    lastN = n;
                } else {
                    if (ss) {
                        wordCnt.set(ss, lastN+1);
                    }
                    
                    wordCnt.set(ss+ch, 1);
                    ss = ch;
                }
            }

            let qualifiedPredef = [],
                qualified = [], i8key, keylenB;
            wordCnt.forEach((cnt, key)=>{
                if (cnt>1) {    //quickly remove low frequency words
                    i8key = utf8enc(key);
                    keylenB = i8key.length;
                    if ((keylenB>1) && (keylenB<=MAX_WORD_LEN_16)) { // 1~15 -> 2~16 (0 not used)
                        (
                            (predLen && predefMap.has(key)) 
                            ? qualifiedPredef 
                            : qualified
                        )
                        .push([key, i8key, keylenB, cnt]);
                    }
                }
            });            

            let qlen = qualified.length,
                qlenAndPred = qlen + predLen,
                u64arr = new BigUint64Array(qlen),
                u32arr = newUint32Array(u64arr.buffer),
                q1, cnt, saveBits,
                idxIn256 = 256 - chUsed,
                idxOut256 = qlenAndPred - chUsed,
                targetbits = 8;     //initial guess, 8bits, how many bits may need

                //todo: better decide targetbits, idxLimit
                if (qlenAndPred>100000)
                    targetbits = 12
                else if (qlenAndPred>50000)
                    targetbits = 11
                else if (qlenAndPred>20000)
                    targetbits = 10
                else if (qlenAndPred>8000)
                    targetbits = 9
                else if (idxIn256<(idxOut256>>>4)) 
                    targetbits = 9;

            for (i=0; i<qlen; i++) {    //prepare data for the sort
                q1 = qualified[i];
                cnt = q1[3];
                keylenB = q1[2];
                saveBits = (cnt*keylenB*8 - cnt*targetbits - keylenB*8); //(cnt*keylenB*6 - cnt*targetbits - keylenB*8); //estimate
                if (saveBits<0) 
                    saveBits = 0;

                j = i<<1;   //i*2
                u32arr[j] = i;
                u32arr[j+1] = saveBits;
            }

            u64arr.sort();  //in place sort

            idxLimit = (1<<targetbits) - chUsed;
            idxLimit += ((idxLimit*5)>>>4); //add 31.25% (5/16) exceed index space
            if (idxLimit>MAX_WLIDX_4096) idxLimit = MAX_WLIDX_4096; //hard max: 12 bits
            idxLimit -= predLen;

            let finalHfList = qualifiedPredef, //[],
                mini = qlen>idxLimit ? qlen-idxLimit : 0;

            i = qlen-1;
            while (i>mini){
                j = i<<1; //i*2
                if (!u32arr[j+1]) break;    //saveBits is 0

                finalHfList.push(qualified[u32arr[j]]);
                i--;
            };

            return finalHfList.map(v=>v[1]);    //[key, i8key, keylenB, cnt]
        }
        ,
        list2SwitchFunc = wi8list=> {  //wi8list element should be Uint8Array
            const MaxKeyBlen = 32;
            let i, j, ch,
                len = wi8list.length,
                i8key, i8keylen,
                maxlevel = 0,
                c2i_level = [], 
                i2c_level = [],
                chCnt_level = newUint16Array(256*MaxKeyBlen);

            for (i=0; i<len; i++) {
                i8key = wi8list[i];
                i8keylen = i8key.length;
                if (i8keylen>MaxKeyBlen) i8keylen = MaxKeyBlen;
                if (i8keylen>maxlevel) maxlevel = i8keylen;

                for (j=0; j<i8keylen; j++) {    //j is level
                    ch = i8key[j];
                    chCnt_level[(j<<8) + ch]++;   //j<<8 = j*256
                }
            }
            
            let c2i, i2c,
                levelIdx;
            for (j=0; j<maxlevel; j++) {
                c2i = newUint16Array(256);
                i2c = newUint8Array(256);

                levelIdx = 0;
                i = j<<8;
                for (ch=0; ch<256; ch++) {
                    if (chCnt_level[i+ch]) {
                        c2i[ch] = levelIdx +1;
                        i2c[levelIdx] = ch;
                        levelIdx ++;
                    }
                }
                c2i_level.push(c2i);
                i2c_level.push(i2c.subarray(0, levelIdx));
            }
            
            let root = new Array(i2c_level[0].length),
                node, nextnode;
            for (i=0; i<len; i++) {
                i8key = wi8list[i];
                i8keylen = i8key.length;
                node = root;
                for (j=0; j<i8keylen; j++) {
                    ch = i8key[j];
                    levelIdx = c2i_level[j][ch] -1;
                    nextnode = node[levelIdx];
                    if (!nextnode) {
                        nextnode = new Array(ArrLen(i2c_level[j+1]));
                        node[levelIdx] = nextnode;
                    }
                    node = nextnode;
                }
                node.wlIdx = i+1;
            }
            return [c2i_level, root];
        }
        ,
        indexReplace = (s, wi8list)=> {
            let i16arr = Uint16Array.from(utf8enc(s)),
                len = ArrLen(i16arr),
                wblens = wi8list.map(v=>v.length),
                wtree = list2SwitchFunc(wi8list),
                c2i_level = wtree[0],
                root = wtree[1],
                maxlevel = c2i_level.length,
                
                i = 0, j, ch, 
                node, nextnode, ni, 
                wlidx, longestIdx,
                smallestIdx,  //smaller index, topper in the list (saves more bits)
                wblen;

            for (; i<len; i++) {
                j=0;
                node = root;
                smallestIdx = maxUINT32;
                longestIdx = 0;
                while(j<maxlevel && i+j<len) {
                    ch = i16arr[i+j];
                    ni = c2i_level[j][ch];  //ni: node index
                    if (ni) {
                        nextnode = node[ni -1];
                        if (nextnode) {
                            node = nextnode;
                            if (node.wlIdx) {
                                longestIdx = node.wlIdx;
                                smallestIdx = longestIdx<smallestIdx ? longestIdx : smallestIdx;
                            }
                        } else
                            break;
                    } else
                        break;  //this char not even indexed
                    j++;
                }
                if (longestIdx) {
                    wlidx = smallestIdx -1;  //smallestIdx / longestIdx
                                                //wblen: 1~15 -> 2~16 (0 not used)
                    wblen = wblens[wlidx] -1;   //       1111  0010   xxxx xxxx
                                                // wlidx(low4) wblen  origval
                    i16arr[i]   |= (wblen<<8) | ((wlidx & 15)<<12);
                    i16arr[i+1] |= (wlidx>>>4)<<8;  //  0000 0011  xxxx xxxx
                    i += wblen; //-1 ahead already  // wlidx(hi8)  origval
                }
            }
            return i16arr;
        }
        ,
        compress = (s, predef) => {
            let 
                predLen = ArrLen(predef),
                wlist = indexing(s, predef),
                wllen = wlist.length,   //how many words in list. (wl: word list)
                i = 0;
            
            const
                u16arr = indexReplace(s, wlist), //Uint16Array.from(utf8enc(s)), //
                u16len = ArrLen(u16arr),
                maxi = wllen+256,
                count = newUint16Array(maxi),
                sort = newUint32Array(maxi),
                c2i = newUint16Array(maxi)
                ;
            
            let j, wlen, wlidx;
            for (i=0; i<u16len; i++) {
                if (u16arr[i]<256) 
                    count[u16arr[i]]++
                else {  //index replace, low4 of high byte of first u16: length of the replaced bytes,
                    wlen = ((u16arr[i]>>>8) & 15) + 1;
                    wlidx = ((u16arr[i+1]>>>8)<<4) | (u16arr[i]>>>12);
                    count[wlidx+256]++; //256+index
                    
                    count[u16arr[i] & 255]++;   //the low byte is the original char
                    count[u16arr[i+1] & 255]++;
                    for (j=2; j<wlen; j++) count[u16arr[i+j]]++;

                    i += wlen-1;
                }
            }

            let k = 0, ch, cnt;

            for (i=0; i<maxi; i++) {   //count limit to 524288 (19 bits) (32-13)
                cnt = count[i];
                if (cnt>UINT19) 
                    cnt = UINT19;
                sort[i] = (cnt<<maxCHBITS) | i; //maxCHBITS = 13, maxi limit to 13 bits
            }

            sort.sort();

            let usedLen, chUsed = 0,
                i2c = newUint16Array(maxi),
                icnt = newUint32Array(maxi);

            i = maxi;
            do {
                j = maxi - i;
                i--;
                ch = sort[i] & UINT13;
                cnt = sort[i] >>> maxCHBITS;
                if (!cnt) {
                    usedLen = j;
                    break;
                }
                c2i[ch] = j;
                i2c[j] = ch;
                icnt[j] = cnt;

                if (ch<256) chUsed++;

            } while(i);

            let usedWllen = usedLen - chUsed,
                maxbits = (usedLen-1).toString(2).length,
                low1bitLimit = (1<<(maxbits-1)),
                reduce = usedLen-low1bitLimit,

                wblens = wlist.map(wb=>ArrLen(wb)),
                wbtotal = wblens.reduce((total,v)=>total+v, 0),
                wbchars = newUint8Array(wbtotal),
                wi2newIdx = newUint16Array(wllen),
                len;

            if ((reduce<(usedWllen-predLen)) && (reduce < (usedLen>>>2))) { //todo: improve this based on better calc
                maxbits -= 1;
                usedLen = low1bitLimit;
                usedWllen = usedLen - chUsed;
            }

            k = predLen;
            wbtotal = 0;
            newIdx = 0;
            for (i=0; i<maxi; i++) {
                ch = i2c[i];
                if (ch>255) {
                    ch -= 256;   //old idx
                    if (ch<predLen) {
                        c2i[ch+256] = newIdx;
                        i2c[newIdx] = ch+256;
                        newIdx++;

                    } else if (k<usedWllen) {
                        c2i[k+256] = newIdx;
                        i2c[newIdx] = k+256;

                        len = wlist[ch].length;
                        wblens[k] = len;

                        k++;         //new wordlist idx
                        newIdx++;

                        wi2newIdx[ch] = k;  //should be after k++; as 0 considered not in wlist

                        for (j=0; j<len; j++) wbchars[wbtotal++] = wlist[ch][j];

                    } //else 
                      //  wi2newIdx[ch] = 0;  
                      //not in the i2c list, no need to do this because wi2newIdx intialed to all 0

                } else {
                    c2i[ch] = newIdx;
                    i2c[newIdx] = ch;
                    newIdx++;
                }
                
            }

            for (i=0; i<predLen; i++) wi2newIdx[i] = i+1;

            icnt = icnt.subarray(0, usedLen);
            i2c = i2c.subarray(0, usedLen);

            if (maxbits<MIN_MAXBITS_5) maxbits = MIN_MAXBITS_5;

            //maxbits for i2c is different, should use 255+usedWllen  maxi
            const
                maxI2cBits = (255+usedWllen).toString(2).length,
                extraI2cBits = maxI2cBits - maxbits;  //maxI2cBits < maxbits is impossible

            const
                planset = planSets[maxbits-3],  //[3,4,5,6,7,8,9,10,11,12,13]
                [bitsPlan, bits] = planset.Select(icnt),
                cmpresFunc = planset.CompressFunc(bitsPlan),
                EXTRA_1BIT = bitsPlan ? 1 : 0,
                STORE_MAX_BITS = maxbits + EXTRA_1BIT;

            //////decision made, now do the data writing//////

            const
                wpos = newUint32Array(1),
                wbi = newUint8Array(1),
                i2c_maxblen = (((maxI2cBits*usedLen -1) >>>3) +1), //>>>3 = /8
                wblensIn4bits = (usedWllen-predLen+1)>>>1,
                wl_maxblen = wbtotal*STORE_MAX_BITS >>>3,
                data_blen = ((bits-1)>>>3) +1,
                i8ret = newUint8Array(
                                        ALGORITHM_1 +
                                        USEDCHLEN_CHBITS_2 +
                                        BITSPLAN_CHARSET_1 +
                                        i2c_maxblen +
                                        WLLEN_2Byte +
                                        wblensIn4bits +
                                        wl_maxblen +
                                        ORIGDATA_LEN_4 +
                                        data_blen
                                     );

            let 
                BORDER = 1<<(bitsPlan ? bitsPlan : maxbits),
                lowMsk = BORDER -1,
                lowBits = bitsPlan ? bitsPlan + EXTRA_1BIT : maxbits,
                upperMsk = ((1<<(maxbits - bitsPlan))-1) << bitsPlan,
                n = usedLen | ((maxbits - MIN_MAXBITS_5)<<13);

            writeN32(128, i8ret, 0, ALGORITHM_1);        //128 is LZW-A
            writeN32(n, i8ret, ALGORITHM_1, _3RD);
            i8ret[_3RD] = bitsPlan | (extraI2cBits<<6);  //charset reserved

            wpos[0] = _3RD + BITSPLAN_CHARSET_1;
            wbi[0] = 0;
            for (i=0; i<usedLen; i++) {
                ch = i2c[i];
                writeBits(  i8ret, wpos, wbi, ch,
                            maxI2cBits //maybe different than maxbits
                         );
            }

            let ChMapEnd = wpos[0] + (wbi[0] ? 1 : 0);

            writeN32(usedWllen-predLen, i8ret, ChMapEnd, ChMapEnd+WLLEN_2Byte);

            wpos[0] = ChMapEnd+WLLEN_2Byte;
            wbi[0] = 0;
            for (i=predLen; i<usedWllen; i++) writeBits(i8ret, wpos, wbi, wblens[i]-2, 4);

            //write words following BitsPlan
            wpos[0] = ChMapEnd + WLLEN_2Byte + wblensIn4bits; //should equal: wpos[0] + (wbi[0] ? 1 : 0)
            wbi[0] = 0;
            for (k=0; k<wbtotal; k++) {
                ch = c2i[wbchars[k]];
                if (ch<BORDER)
                    writeBits(  i8ret, wpos, wbi, ch, lowBits)
                else {
                    ch = (ch & lowMsk) | BORDER | ((ch & upperMsk)<<1);
                    writeBits(  i8ret, wpos, wbi, ch, STORE_MAX_BITS);
                }
            }

            let dStart = wpos[0] + (wbi[0] ? 1 : 0);
            writeN32(u16len, i8ret, dStart, dStart + ORIGDATA_LEN_4);
            
            const 
                dlen = cmpresFunc(u16arr, c2i, i8ret.subarray(dStart + ORIGDATA_LEN_4), wi2newIdx);
            
            return i8ret.subarray(0, dStart + ORIGDATA_LEN_4 + dlen +1);
        }
        ,
        uncompress = (i8arr, predef) => {
            const 
                i8len = ArrLen(i8arr);
            if (i8len < ALGORITHM_1 + USEDCHLEN_CHBITS_2 + 
                        BITSPLAN_CHARSET_1 + 
                        WLLEN_2Byte + ORIGDATA_LEN_4
                ) return;

            const
                algorithm = readN32(i8arr, 0, ALGORITHM_1),
                i2clen_bitsplan = readN32(i8arr, ALGORITHM_1, _3RD),
                i2clen = i2clen_bitsplan & UINT13,
                maxbits = (i2clen_bitsplan>>>13) + MIN_MAXBITS_5,
                bPlanChset = readN32(i8arr, _3RD, _3RD + BITSPLAN_CHARSET_1),
                bitsPlan = bPlanChset & 15,
                maxI2cBits = maxbits + (bPlanChset>>>6),
                BORDER = 1<<(bitsPlan ? bitsPlan : maxbits),
                lowMsk = BORDER -1,
                lowBits = bitsPlan ? bitsPlan+1 : maxbits,
                upBits = maxbits - bitsPlan,
                rpos = newUint32Array(1),
                rbi = newUint8Array(1),
                i2c = newUint16Array(i2clen),
                valAtPos = ()=>i8arr[rpos[0]];

            if (algorithm!==128) throwerr(DataCorruptedErr, 'only LZW-A');

            if (bitsPlan>=maxbits)
                throwerr(DataCorruptedErr, 'WrongBitsPlan');

            rpos[0] = _3RD + BITSPLAN_CHARSET_1;
            rbi[0] = 0;

            let i=0, j, ch;
            for (; i<i2clen; i++)
                i2c[i] = readBits(i8arr, rpos, rbi, maxI2cBits);

            if (rbi[0] && (valAtPos()>>>rbi[0]))
                throwerr(DataCorruptedErr, 'Aft_i2c');

            let ChMapEnd = rpos[0] + (rbi[0] ? 1 : 0),
                wllen = readN32(i8arr, ChMapEnd, ChMapEnd + WLLEN_2Byte),
                wblens = newUint8Array(wllen);

            if (wllen>MAX_WLIDX_4096)
                throwerr(DataCorruptedErr, 'Wllen>4096');

            rpos[0] = ChMapEnd + WLLEN_2Byte;
            rbi[0] = 0;
            for (i=0; i<wllen; i++)
                wblens[i] = readBits(i8arr, rpos, rbi, 4) + 2;  //4bits a length

            if (rbi[0] && (valAtPos() & 240))   //240: 1111 0000, the high 4 bits
                throwerr(DataCorruptedErr, 'AftWblens');

            const 
                wlistChTotal = wblens.reduce((total, v)=>total+v, 0),
                wlistChars = newUint8Array(wlistChTotal);
            
            rpos[0] += rbi[0] ? 1 : 0;
            rbi[0] = 0;
            for (i=0; i<wlistChTotal; i++) {
                ch = readBits(i8arr, rpos, rbi, lowBits);
                if (ch & BORDER) {
                    ch &= lowMsk;
                    ch |= readBits(i8arr, rpos, rbi, upBits)<<bitsPlan;
                }
                wlistChars[i] = i2c[ch];
            }

            if (rbi[0] && (valAtPos()>>>rbi[0]))
                throwerr(DataCorruptedErr, 'Aft_wl_chars');

            let
                wlist = new Array(wllen);

            j = 0;
            for(i=0; i<wllen; i++) 
                wlist[i] = wlistChars.subarray(j, j+=wblens[i]);

            if (predef) 
                wlist = predef.map(s=>utf8enc(s)).concat(wlist);

            rpos[0] += rbi[0] ? 1 : 0;
            rbi[0] = 0;
                
            const
                dstart = rpos[0] + ORIGDATA_LEN_4,
                planset = planSets[maxbits-3],
                uncompress = planset.UncompressFunc(bitsPlan),
                origlen = readN32(i8arr, rpos[0], dstart),
                i8ret = uncompress(i8arr.subarray(dstart), i2c, wlist, origlen);

            return utf8dec(i8ret);
        }
        ;

    self.Idxing = indexing;
    self.MkFunction = list2SwitchFunc;
    self.IdxReplace = indexReplace;
    self.Compress = compress;
    self.Uncompress = uncompress;
}

LZW_A = new LZWIndexString();

if (typeof window === 'undefined') 
    module.exports = LZW_A;

})();





////////////test////////////
// let fs = require('fs'),
//     s = fs.readFileSync(__dirname+'/ccon2.min.js', 'utf8');

// console.log('orig size:', s.length);

// let t = new Date().getTime(),
//     i8arr = LZW_A.Compress(s)//,['let ', 'const ', 'new ', 'function ', 'return', '.subarray(', 'case ', 'else'])
//     ,
//     t2 = new Date().getTime()
//     ,
//     s2 = LZW_A.Uncompress(i8arr)//,['let ', 'const ', 'new ', 'function ', 'return', '.subarray(', 'case ', 'else'])
//     ,
//     t3 = new Date().getTime()
//     ;

// console.log('compressed size:', i8arr.length);
// console.log('compress time ms:', t2 - t);
// console.log('uncompress time ms:', t3 - t2);
// console.log('orig===uncompressed? ', s===s2);
// if (s!==s2) console.log(s2);

