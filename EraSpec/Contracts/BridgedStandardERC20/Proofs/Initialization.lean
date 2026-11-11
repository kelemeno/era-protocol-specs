import EraSpec.Contracts.BridgedStandardERC20.Properties.Initialization

namespace Contracts.BridgedStandardERC20

theorem initialization_binds_inputs {s t : InitState} {caller origin : Address}
    {asset : UInt256} {decoded : Bool}
    (h : initializeToken s caller asset origin decoded = some t) :
    Properties.initialization_binds_inputs h := by
  unfold Properties.initialization_binds_inputs
  simp only [initializeToken] at h
  split_ifs at h with hallowed
  · injection h with ht
    subst t
    exact ⟨rfl, rfl, rfl, hallowed.1.2, rfl⟩

theorem initialization_preserves_balances {s t : InitState} {caller origin : Address}
    {asset : UInt256} {decoded : Bool}
    (h : initializeToken s caller asset origin decoded = some t) :
    Properties.initialization_preserves_balances h := by
  unfold Properties.initialization_preserves_balances
  simp only [initializeToken] at h
  split_ifs at h with hallowed
  · injection h with ht
    subst t
    exact ⟨rfl, rfl⟩

theorem initialization_preserves_ledger {s t : InitState} {caller origin : Address}
    {asset : UInt256} {decoded : Bool} (hw : WellFormed s.token)
    (h : initializeToken s caller asset origin decoded = some t) :
    Properties.initialization_preserves_ledger hw h := by
  unfold Properties.initialization_preserves_ledger
  simp only [initializeToken] at h
  split_ifs at h with hallowed
  · have ht' := Option.some.inj h
    cases ht'
    exact hw

theorem fresh_initialization_enabled (caller origin : Address) (asset : UInt256)
    (ho : origin ≠ 0) :
    Properties.fresh_initialization_enabled caller origin asset ho := by
  let t : InitState :=
    ⟨{ freshProxy.token with config := ⟨caller, origin, asset⟩ }, 1⟩
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · simp [initializeToken, InitializeAllowed, freshProxy, t, ho]
  · change WellFormed t.token
    dsimp only [t, freshProxy, empty]
    refine ⟨?_, ?_, rfl⟩
    · exact Finset.sum_const_zero
    · norm_num [UInt256.size]
  · simp [t, freshProxy, empty]
  · intro a
    rfl

theorem initialization_once {s t : InitState} {caller origin : Address}
    {asset : UInt256} {decoded : Bool}
    (h : initializeToken s caller asset origin decoded = some t)
    (nextCaller nextOrigin : Address) (nextAsset : UInt256) (nextDecoded : Bool) :
    Properties.initialization_once h nextCaller nextOrigin nextAsset nextDecoded := by
  unfold Properties.initialization_once
  simp only [initializeToken] at h ⊢
  split_ifs at h with hallowed
  · injection h with ht
    subst t
    simp [InitializeAllowed]

theorem implementation_initialization_disabled (caller origin : Address)
    (asset : UInt256) (decoded : Bool) :
    Properties.implementation_initialization_disabled caller origin asset decoded := by
  unfold Properties.implementation_initialization_disabled initializeToken
  simp [disabledImplementation, InitializeAllowed]

theorem failed_metadata_initialization {s : InitState} (caller origin : Address)
    (asset : UInt256) :
    Properties.failed_metadata_initialization (s := s) caller origin asset := by
  unfold Properties.failed_metadata_initialization initializeToken
  simp

end Contracts.BridgedStandardERC20
