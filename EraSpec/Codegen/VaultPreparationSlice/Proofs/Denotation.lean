import EraSpec.Codegen.VaultPreparationSlice.Specs.Correspondence
import EraSpec.Codegen.BridgedTokenSlice.Proofs.Refinement
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashEncoding

/-!
# What the programs do, in closed form

Helper results for `Refinement.lean`, with no model in them:

* `xcall_bridgeBurn`: the vault's `bridgeBurn`, for any machine, as nested conditions on
  its inputs and on what the machine's calls and hooks return (`burnDenote`), obtained by
  evaluating the interpreter one statement at a time;
* `xcall_view`: every other vault function changes nothing;
* the token program's functions as the bridged-token slice's;
* the machine's calls and hooks, and their inversion;
* `abi.encode` of the burn data and the mint tuple, and reading their words back.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.BridgedStandardERC20 (Address)
open Codegen.BridgedTokenSlice (addrWord)
open Contracts.NativeTokenVaultBase (BurnData MintData)

variable {W : Type}

/-! ## `bridgeBurn` -/

theorem find_bridgeBurn : vaultProgram.find "bridgeBurn" = some bridgeBurn := rfl

/-- The burn data's three words: amount, receiver, token hint. -/
def bAmount (data : Bytes) : Word := (fromBytes (data.take 32) : Word)
def bReceiver (data : Bytes) : ℕ := fromBytes ((data.drop 32).take 32)
def bHint (data : Bytes) : ℕ := fromBytes ((data.drop 64).take 32)

/-- The token a hint names: the registered one for a zero hint. -/
def resolve (st : Storage) (a hint : Word) : Word :=
  if hint = 0 then st.maps "_tokenAddress" a else hint

/-- `bridgeBurn` from the token check on, for the decoded words. -/
def burnTail (M : Machine W) (e : Env) (c a oc amt rcv tok : Word) (st : Storage) (w : W) :
    Except XFailure (XSuccess W) :=
  if tok = 0 then .error (.data (.custom "ZeroAddress" []))
  else if a ≠ st.maps "_assetIdOf" tok then
    .error (.data (.custom "AssetIdMismatch" [st.maps "_assetIdOf" tok, a]))
  else if amt = 0 then .error (.data (.custom "AmountMustBeGreaterThanZero" []))
  else if st.maps "_originChainId" a = e.chainId then .error (.data (.custom "OutsideSlice" []))
  else if a = st.scalars "_baseTokenAssetId" then .error (.data (.custom "OutsideSlice" []))
  else match M.hook w "_handleBridgeToChain" [c, a, amt] with
    | .error err => .error err
    | .ok (w1, _) =>
      if e.value ≠ 0 then .error (.data (.custom "NonEmptyMsgValue" []))
      else match M.call w1 e.self tok "bridgeBurn" [oc, amt] with
        | .error err => .error err
        | .ok (w2, _, logs1) =>
          match M.call w2 e.self tok "originToken" [] with
          | .error err => .error err
          | .ok (w3, .word ot, logs2) =>
              if ot = 0 then .error (.data (.custom "ZeroAddress" []))
              else if st.maps "_originChainId" a = 0 then .error (.data (.custom "ZeroAddress" []))
              else match M.hook w3 "_getERC20GettersInner" [tok, st.maps "_originChainId" a] with
                | .error err => .error err
                | .ok (w4, .bytes md) =>
                    .ok ⟨st, w4, logs1 ++ logs2 ++ [⟨e.self, ⟨"BridgeBurn", [c, a, oc, rcv, amt]⟩⟩],
                      some (.bytes (abiEncode [.word oc, .word rcv, .word ot, .word amt, .bytes md]))⟩
                | .ok (_, .none) | .ok (_, .word _) => .error .empty
          | .ok (_, .none, _) | .ok (_, .bytes _, _) => .error .empty

/-- **WHAT `bridgeBurn` DOES**, for any machine. -/
def burnDenote (M : Machine W) (e : Env) (c l2v a oc : Word) (data : Bytes) (st : Storage)
    (w : W) : Except XFailure (XSuccess W) :=
  if l2v ≠ 0 then .error (.data (.custom "NonEmptyMsgValue" []))
  else if e.sender ≠ st.scalars "_assetRouter" then .error (.data (.custom "Unauthorized" [e.sender]))
  else if st.scalars "_paused" ≠ 0 then .error (.data (.message "Pausable: paused"))
  else if data.length ≠ 96 then .error (.data (.custom "InvalidNTVBurnData" []))
  else if ¬ (bReceiver data < 2 ^ 160 ∧ bHint data < 2 ^ 160) then .error .empty
  else burnTail M e c a oc (bAmount data) (bReceiver data : Word)
    (resolve st a (bHint data : Word)) st w

theorem decode_three (data : Bytes) (env : String → Word) (hl : data.length = 96) :
    decodeInto data env [⟨"amount", .uint256⟩, ⟨"receiver", .address⟩,
        ⟨"parsedTokenAddress", .address⟩] =
      if bReceiver data < 2 ^ 160 ∧ bHint data < 2 ^ 160 then
        some (upd (upd (upd env "amount" (bAmount data)) "receiver" (bReceiver data : Word))
          "parsedTokenAddress" (bHint data : Word))
      else none := by
  by_cases h1 : bReceiver data < 2 ^ 160 <;> by_cases h2 : bHint data < 2 ^ 160 <;>
  simp only [bReceiver, bHint, Nat.reducePow] at h1 h2 <;>
  simp [decodeInto, fits, bAmount, bReceiver, bHint, List.drop_drop, hl, h1, h2]

theorem upd_self {α : Type} (f : String → α) (k : String) : upd f k (f k) = f := by
  funext x
  by_cases h : x = k <;> simp [upd, h]

theorem execX_resolveToken (M : Machine W) (self : Word) (f : XFrame W) :
    execX M self f resolveToken =
      .ok ({ f with cx := { f.cx with env := (upd f.cx.env "parsedTokenAddress"
        (resolve f.st (f.cx.env "_assetId") (f.cx.env "parsedTokenAddress"))) } }, none) := by
  by_cases h : f.cx.env "parsedTokenAddress" = 0 <;>
    simp [execX, resolveToken, evalCond, evalExpr, resolve, h, zeroAddr, upd_self]

/-- Evaluate the vault program as far as the case hypotheses in context decide it. -/
local macro "burn_simp" : tactic =>
  `(tactic| simp [xcall, find_bridgeBurn, bindXParams, bridgeBurn, execXBody, execX, execStmt,
      evalExpr, evalCond, upd, reasonFailure, evalList, zero, zeroAddr, msgValue, blockChainId,
      decode_three, -Nat.reducePow, execX_resolveToken, bindRet, evalAbiArgs, evalAbiArg, *])

set_option linter.unusedSimpArgs false in
/-- **THE INTERPRETER EVALUATES `bridgeBurn` TO `burnDenote`.** -/
theorem xcall_bridgeBurn (M : Machine W) (e : Env) (c l2v a oc : Word) (data : Bytes)
    (st : Storage) (w : W) :
    xcall M vaultProgram "bridgeBurn" e [.word c, .word l2v, .word a, .word oc, .bytes data] st w =
      some (burnDenote M e c l2v a oc data st w) := by
  unfold burnDenote
  obtain h1 | h1 := ne_or_eq l2v 0
  · burn_simp
  obtain h2 | h2 := ne_or_eq e.sender (st.scalars "_assetRouter")
  · burn_simp
  obtain h3 | h3 := ne_or_eq (st.scalars "_paused") 0
  · burn_simp
  obtain h4 | h4 := ne_or_eq data.length 96
  · burn_simp
  obtain h5 | h5 := em' (bReceiver data < 2 ^ 160 ∧ bHint data < 2 ^ 160)
  · burn_simp
  simp only [h1, h2, h3, h4, h5, ne_eq, not_true_eq_false, ite_false, not_false_eq_true,
    and_self]
  unfold burnTail
  by_cases h7 : resolve st a ↑(bHint data) = 0
  · burn_simp
  obtain h8 | h8 := ne_or_eq (st.maps "_assetIdOf" (resolve st a ↑(bHint data))) a
  · have h8' := Ne.symm h8
    burn_simp
  by_cases h9 : bAmount data = 0
  · burn_simp
  by_cases h10 : st.maps "_originChainId" a = e.chainId
  · burn_simp
  by_cases h11 : st.scalars "_baseTokenAssetId" = a
  · burn_simp
  have h11' : ¬ a = st.scalars "_baseTokenAssetId" := fun h => h11 h.symm
  rcases hk : M.hook w "_handleBridgeToChain" [c, a, bAmount data] with err | ⟨w1, r1⟩
  · burn_simp
  obtain h12 | h12 := ne_or_eq e.value 0
  · burn_simp
  rcases hc1 : M.call w1 e.self (resolve st a ↑(bHint data)) "bridgeBurn" [oc, bAmount data]
    with err | ⟨w2, r2, logs1⟩
  · burn_simp
  rcases hc2 : M.call w2 e.self (resolve st a ↑(bHint data)) "originToken" [] with
    err | ⟨w3, r3, logs2⟩
  · burn_simp
  rcases r3 with _ | ot | b
  · burn_simp
  swap
  · burn_simp
  by_cases h13 : ot = 0
  · burn_simp
  by_cases h14 : st.maps "_originChainId" a = 0
  · rw [h14] at h10
    burn_simp
  rcases hk2 : M.hook w3 "_getERC20GettersInner" [resolve st a ↑(bHint data), st.maps "_originChainId" a]
    with err | ⟨w4, r4⟩
  · burn_simp
  rcases r4 with _ | v | md
  · burn_simp
  · burn_simp
  · burn_simp

/-! ## The views -/

/-- A vault view's body is one `return` of a storage read: it changes nothing. -/
theorem xcall_view {M : Machine W} {fname : String} {e : Env} {args : List AbiVal}
    {st : Storage} {w : W} {res : XSuccess W} (hname : fname ≠ "bridgeBurn")
    (h : xcall M vaultProgram fname e args st w = some (.ok res)) :
    res.st = st ∧ res.w = w ∧ res.logs = [] := by
  unfold xcall at h
  split at h
  · cases h
  rename_i fn hfind
  have hmem := List.mem_of_find?_eq_some hfind
  have hfn : fn.name = fname := by simpa using List.find?_some hfind
  simp only [vaultProgram, List.mem_cons, List.not_mem_nil, or_false] at hmem
  split at h
  · cases h
  rename_i env benv _
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact absurd hfn.symm hname
  all_goals
    simp only [pausedFn, tokenAddressFn, assetIdOfFn, originChainIdFn, true_and,
      Option.some.injEq] at h
    simp only [execXBody, execX, execStmt, evalExpr] at h
    split_ifs at h
    cases h
    simp

/-! ## The token program is the bridged-token slice, plus two getters -/

theorem tokenProgram_find_bridgeMint :
    tokenProgram.find "bridgeMint" = some BridgedTokenSlice.bridgeMint := rfl
theorem tokenProgram_find_bridgeBurn :
    tokenProgram.find "bridgeBurn" = some BridgedTokenSlice.bridgeBurn := rfl
theorem tokenProgram_find_transfer :
    tokenProgram.find "transfer" = some BridgedTokenSlice.transfer := rfl
theorem tokenProgram_find_balanceOf :
    tokenProgram.find "balanceOf" = some BridgedTokenSlice.balanceOf := rfl
theorem tokenProgram_find_totalSupply :
    tokenProgram.find "totalSupply" = some BridgedTokenSlice.totalSupply := rfl
theorem tokenProgram_find_nativeTokenVault :
    tokenProgram.find "nativeTokenVault" = some BridgedTokenSlice.nativeTokenVault := rfl
theorem tokenProgram_find_originToken : tokenProgram.find "originToken" = some originTokenFn := rfl
theorem tokenProgram_find_assetId : tokenProgram.find "assetId" = some assetIdFn := rfl

/-- A call depends on the contract only through which function a name finds. -/
theorem call_congr {c c' : Contract} {fname : String} (h : c.find fname = c'.find fname) :
    Codegen.call c fname = Codegen.call c' fname := by
  funext snd args st
  simp only [Codegen.call, h]

theorem tokenCall_bridgeMint :
    Codegen.call tokenProgram "bridgeMint" = Codegen.call BridgedTokenSlice.program "bridgeMint" :=
  call_congr rfl
theorem tokenCall_bridgeBurn :
    Codegen.call tokenProgram "bridgeBurn" = Codegen.call BridgedTokenSlice.program "bridgeBurn" :=
  call_congr rfl
theorem tokenCall_transfer :
    Codegen.call tokenProgram "transfer" = Codegen.call BridgedTokenSlice.program "transfer" :=
  call_congr rfl
theorem tokenCall_balanceOf :
    Codegen.call tokenProgram "balanceOf" = Codegen.call BridgedTokenSlice.program "balanceOf" :=
  call_congr rfl
theorem tokenCall_totalSupply :
    Codegen.call tokenProgram "totalSupply" = Codegen.call BridgedTokenSlice.program "totalSupply" :=
  call_congr rfl
theorem tokenCall_nativeTokenVault :
    Codegen.call tokenProgram "nativeTokenVault" =
      Codegen.call BridgedTokenSlice.program "nativeTokenVault" :=
  call_congr rfl

theorem tokenCall_originToken (st : Storage) (snd : Word) :
    Codegen.call tokenProgram "originToken" snd [] st =
      some (.ok ⟨st, [], some (st.scalars "_originToken")⟩) := by
  simp [Codegen.call, tokenProgram_find_originToken, bindParams, originTokenFn, execBody, execStmt,
    evalExpr]

theorem tokenCall_assetId (st : Storage) (snd : Word) :
    Codegen.call tokenProgram "assetId" snd [] st =
      some (.ok ⟨st, [], some (st.scalars "_assetId")⟩) := by
  simp [Codegen.call, tokenProgram_find_assetId, bindParams, assetIdFn, execBody, execStmt,
    evalExpr]

/-! ## The machine -/

variable {Acct : Type}

theorem machine_call_token_ok {T : Word} {ch : CHooks Acct} {w : World Acct} {self : Word}
    {fname : String} {args : List Word} {r : Success}
    (hr : Codegen.call tokenProgram fname self args w.token = some (.ok r)) :
    (machine T ch).call w self T fname args =
      .ok (⟨r.st, w.acct⟩, retOf r.ret, r.logs.map (XLog.mk T)) := by
  simp [machine, hr]

theorem machine_call_other {T target : Word} (ch : CHooks Acct) (w : World Acct) (self : Word)
    (fname : String) (args : List Word) (h : target ≠ T) :
    (machine T ch).call w self target fname args = .error .empty := by
  simp [machine, h]

theorem machine_hook_account_of {T : Word} {ch : CHooks Acct} {w : World Acct} {c a m : Word}
    {acc : Acct} (h : ch.account w.acct w.token c a m = .ok acc) :
    (machine T ch).hook w "_handleBridgeToChain" [c, a, m] = .ok (⟨w.token, acc⟩, .none) := by
  simp [machine, h]

theorem machine_hook_metadata_of {T : Word} {ch : CHooks Acct} {w : World Acct} {o : Word}
    {b : Bytes} (h : ch.metadata w.token o = .ok b) :
    (machine T ch).hook w "_getERC20GettersInner" [T, o] = .ok (w, .bytes b) := by
  simp [machine, h]

/-- Inversion: a successful call went to the token, whose code succeeded. -/
theorem machine_call_ok {T target : Word} {ch : CHooks Acct} {w w' : World Acct} {self : Word}
    {fname : String} {args : List Word} {ret : Ret} {logs : List XLog}
    (h : (machine T ch).call w self target fname args = .ok (w', ret, logs)) :
    target = T ∧ ∃ r, Codegen.call tokenProgram fname self args w.token = some (.ok r) ∧
      w' = ⟨r.st, w.acct⟩ ∧ ret = retOf r.ret ∧ logs = r.logs.map (XLog.mk T) := by
  by_cases ht : target = T
  · subst ht
    simp only [machine, ↓reduceIte] at h
    split at h
    · rename_i r hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨rfl, r, hr, h.1.symm, h.2.1.symm, h.2.2.symm⟩
    · cases h
    · cases h
  · rw [machine_call_other _ _ _ _ _ ht] at h
    cases h

/-- Inversion: a successful accounting hook is a successful `account`, writing only the
accounting state. -/
theorem machine_hook_account_ok {T : Word} {ch : CHooks Acct} {w w' : World Acct}
    {c a m : Word} {ret : Ret}
    (h : (machine T ch).hook w "_handleBridgeToChain" [c, a, m] = .ok (w', ret)) :
    ∃ acc, ch.account w.acct w.token c a m = .ok acc ∧ w' = ⟨w.token, acc⟩ := by
  simp only [machine, ↓reduceIte] at h
  split at h
  · rename_i acc hacc
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨acc, hacc, h.1.symm⟩
  · cases h

/-- Inversion: a successful metadata hook was for the token, and `metadata` succeeded. -/
theorem machine_hook_metadata_ok {T t : Word} {ch : CHooks Acct} {w w' : World Acct}
    {o : Word} {ret : Ret}
    (h : (machine T ch).hook w "_getERC20GettersInner" [t, o] = .ok (w', ret)) :
    t = T ∧ ∃ b, ch.metadata w.token o = .ok b ∧ w' = w ∧ ret = .bytes b := by
  by_cases ht : t = T
  · subst ht
    rcases hb : ch.metadata w.token o with e | b
    · simp [machine, hb] at h
    · simp [machine, hb] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, b, rfl, rfl, rfl⟩
  · simp [machine, ht] at h

/-! ## Words and bytes -/

theorem length_word32 (n : ℕ) : (word32 n).length = 32 :=
  AttackVectors.BundleHashEncoding.length_toBytesBE 32 n

theorem fromBytes_word32 {n : ℕ} (h : n < 2 ^ 256) : fromBytes (word32 n) = n :=
  AttackVectors.BundleHashEncoding.fromBytesBE_toBytesBE (k := 32) (by simpa using h)

theorem fromBytes_word32_val (w : Word) : fromBytes (word32 w.val) = w.val :=
  fromBytes_word32 (by simpa [UInt256.size] using w.isLt)

/-- Writing back the number a byte string reads as gives the byte string. -/
theorem toBytesBE_fromBytesBE : ∀ (k : ℕ) (l : Bytes), l.length = k →
    AttackVectors.BundleHashEncoding.toBytesBE k (AttackVectors.BundleHashEncoding.fromBytesBE l) = l
  | 0, l, h => by
      rw [List.length_eq_zero_iff] at h; subst h; rfl
  | k + 1, l, h => by
      obtain ⟨l', x, rfl⟩ : ∃ l' x, l = l' ++ [x] := by
        rcases List.eq_nil_or_concat l with h0 | ⟨l', x, hx⟩
        · subst h0; simp at h
        · exact ⟨l', x, by simpa using hx⟩
      have hl' : l'.length = k := by simpa using h
      rw [AttackVectors.BundleHashEncoding.toBytesBE,
        AttackVectors.BundleHashEncoding.fromBytesBE_append_singleton]
      have hx : x.toNat < 256 := x.toNat_lt
      have hdiv : (AttackVectors.BundleHashEncoding.fromBytesBE l' * 256 + x.toNat) / 256 =
          AttackVectors.BundleHashEncoding.fromBytesBE l' := by omega
      have hmod : (AttackVectors.BundleHashEncoding.fromBytesBE l' * 256 + x.toNat) % 256 =
          x.toNat := by omega
      rw [hdiv, hmod, toBytesBE_fromBytesBE k l' hl']
      simp

theorem word32_fromBytes {l : Bytes} (h : l.length = 32) : word32 (fromBytes l) = l :=
  toBytesBE_fromBytesBE 32 l h

theorem fromBytes_lt_pow (l : Bytes) : fromBytes l < 256 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [fromBytes, AttackVectors.BundleHashEncoding.fromBytesBE]
  | append_singleton l x ih =>
    rw [fromBytes, AttackVectors.BundleHashEncoding.fromBytesBE_append_singleton]
    have hx := x.toNat_lt
    simp only [List.length_append, List.length_singleton, pow_succ]
    have ih' : AttackVectors.BundleHashEncoding.fromBytesBE l + 1 ≤ 256 ^ l.length := ih
    nlinarith

theorem fromBytes_lt {l : Bytes} (h : l.length = 32) : fromBytes l < 2 ^ 256 := by
  simpa [h] using fromBytes_lt_pow l

theorem encodeBurnData_eq (b : BurnData) :
    encodeBurnData b = word32 b.amount.val ++ word32 b.receiver.val ++ word32 b.tokenHint.val := by
  simp [encodeBurnData, abiEncode, heads, AbiVal.tail, addrWord]

theorem encodeMintData_eq (m : MintData) :
    encodeMintData m = word32 m.originalCaller.val ++ word32 m.remoteReceiver.val ++
      word32 m.originToken.val ++ word32 m.amount.val ++ word32 160 ++
      word32 m.metadata.length ++ pad32 m.metadata := by
  simp [encodeMintData, abiEncode, heads, AbiVal.tail, addrWord]

theorem take_word32 (n : ℕ) (l : Bytes) : (word32 n ++ l).take 32 = word32 n :=
  List.take_left' (length_word32 n)

theorem drop_word32 (n : ℕ) (l : Bytes) : (word32 n ++ l).drop 32 = l :=
  List.drop_left' (length_word32 n)

theorem natCast_addr (a : Address) : ((a.val : ℕ) : Word) = addrWord a := by
  apply Fin.ext
  simp only [addrWord, Fin.val_natCast]
  exact Nat.mod_eq_of_lt (lt_trans a.isLt (by decide))

theorem natCast_val (w : Word) : ((w.val : ℕ) : Word) = w := Fin.cast_val_eq_self w

theorem length_encodeBurnData (b : BurnData) : (encodeBurnData b).length = 96 := by
  simp [encodeBurnData_eq]

theorem bAmount_encodeBurnData (b : BurnData) : bAmount (encodeBurnData b) = b.amount := by
  rw [bAmount, encodeBurnData_eq, List.append_assoc, take_word32, fromBytes_word32_val,
    natCast_val]

theorem bReceiver_encodeBurnData (b : BurnData) : bReceiver (encodeBurnData b) = b.receiver.val := by
  rw [bReceiver, encodeBurnData_eq, List.append_assoc, drop_word32, take_word32]
  exact fromBytes_word32 (lt_trans b.receiver.isLt (by decide))

theorem bHint_encodeBurnData (b : BurnData) : bHint (encodeBurnData b) = b.tokenHint.val := by
  have h64 : (64 : ℕ) = 32 + 32 := rfl
  rw [bHint, encodeBurnData_eq, List.append_assoc, h64, ← List.drop_drop, drop_word32,
    drop_word32, List.take_of_length_le (by simp)]
  exact fromBytes_word32 (lt_trans b.tokenHint.isLt (by decide))

/-- The burn data the decoded words stand for is the bytes they were decoded from. -/
theorem encodeBurnData_decoded {data : Bytes} (hl : data.length = 96)
    (hr : bReceiver data < 2 ^ 160) (hh : bHint data < 2 ^ 160) :
    encodeBurnData ⟨bAmount data, ⟨bReceiver data, hr⟩, ⟨bHint data, hh⟩⟩ = data := by
  have h1 : (data.take 32).length = 32 := by simp [hl]
  have h2 : ((data.drop 32).take 32).length = 32 := by simp [hl]
  have h3 : (data.drop 64).length = 32 := by simp [hl]
  have hsplit : data = data.take 32 ++ ((data.drop 32).take 32 ++ data.drop 64) := by
    have h64 : (64 : ℕ) = 32 + 32 := rfl
    rw [h64, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have hamt : (bAmount data).val = fromBytes (data.take 32) := by
    simp only [bAmount, Fin.val_natCast]
    exact Nat.mod_eq_of_lt (by simpa [UInt256.size] using fromBytes_lt h1)
  have hhint : bHint data = fromBytes ((data.drop 64).take 32) := rfl
  rw [List.take_of_length_le (le_of_eq h3)] at hhint
  rw [encodeBurnData_eq]
  simp only [hamt]
  rw [word32_fromBytes h1, show bReceiver data = fromBytes ((data.drop 32).take 32) from rfl,
    word32_fromBytes h2, hhint, word32_fromBytes h3, List.append_assoc, ← hsplit]

theorem mintAmount_encodeMintData (m : MintData) :
    mintAmount (some (.bytes (encodeMintData m))) = m.amount.val := by
  have h96 : (96 : ℕ) = 32 + 32 + 32 := rfl
  simp only [mintAmount, encodeMintData_eq, List.append_assoc]
  rw [h96, ← List.drop_drop, ← List.drop_drop, drop_word32, drop_word32, drop_word32,
    take_word32, fromBytes_word32_val]

/-- The original caller's word: the first head. -/
theorem first_word_encodeMintData (m : MintData) :
    fromBytes ((encodeMintData m).take 32) = m.originalCaller.val := by
  simp only [encodeMintData_eq, List.append_assoc]
  rw [take_word32]
  exact fromBytes_word32 (lt_trans m.originalCaller.isLt (by decide))

end Codegen.VaultPreparationSlice
