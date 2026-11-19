# Headline tagging for unit imt, to run from the repo root once EraSpec/Core/Headline.lean has
# landed. It adds @[headline]/@[witness]/@[countermodel] to the listed Properties defs.
# Names under History (Pinned*, Padding*, CThreeLeafWitness) are matched by short name.

import re,glob,sys
T={'headline':'''ReclaimableIffAbsentV35 DeliveredAvailableForeverV35 DeliveryExactlyOnceV35 HonestInsertNeverSearchRevertsV35
DeliveredRefundLocatesCollisionOrPaddingHit BreakFreeGateDichotomy DeployedGateLiveness
CTxRunAtV35StoredRootIsPublished CTxRunAtV35ContractProofsAtStoredRoot CTxRunAtV35EmptySlotLocatesPadding
CTxRunAtV35ReclaimableIffAbsent CTxRunAtV35KeysMono CTxRunAtV35InitL2AtMostOnce
NonInclusionAtHeadIsAbsentOrKeccakCollision ProofsExclusiveAtHeadOrKeccakCollision InsertAtHeadEnabledIff''',
'witness':'''RunV35Satisfiable RunV35PremisesMetV35 WalkPremisesSatisfiableV35 BreakFreeGateRunWitness FinalityPremisesWitness
DedicatedPaddingPremiseWitness ReachedSnapshotShapesWitness StoredRootAtPaddingWitness genesisInsertHistory_guarded
StaleHintCRunWitnessAtV35 NonInclusionAtHeadWitness ContractProofsAtStoredRootAtHead PaddingAtHeadThreeLeafRun
InsertAtHeadWitness StaleHintRunWitnessAtHead ChainTreeRunCallsV35 GenesisRunWitness HThreeRunWitness''',
'countermodel':'''forged_padding_witness_breaks_exclusivity padding_leaf_forges_every_delivered forged_padding_witness_pinned
padding_leaf_forges_on_guarded_history weak_window_without_dedup_breaks_keyInj below_window_insert_breaks_windowPos
resetHistory_forgets resetHistory_not_evolution DedicatedPaddingReadingsFailUnderToyHashes ToyEmptyIndexRefundWitness
ToyFullSnapshotRefundWitness PinBoundRevertsWhereV35InsertsV35 PinForgeryAtHeadFiresOnCollision LeafCollisionAtHeadFires
NodeCollisionAtHeadFires OutOfRangeIndexAtHeadWitness TreeRootBreakEveryCaseFires PaddingForgeryAtV35Witness
GuardlessReinitBreaksExclusivity TreeRootBreakAtHeadNeedsNextIndexBound HashAssumptionsUnsatisfiable
PinnedGateAcceptsEveryValueBelowCapacity PinnedGateAcceptsEveryValueOffPowersOfTwo PinnedCounterexampleMeetsCapstoneHypotheses
PinnedReclaimDichotomyReadingFails PinnedDeliveryFinalityReadingFails PaddingCollisionForgesAbsence
PaddingCollisionRefundsDeliveredLeg PaddingCountermodelLocatesPaddingHit PaddingCountermodelExactlyPaddingHit
PaddingForgeryAtOwnHeight CThreeLeafWitness'''}
tag={n:t for t,v in T.items() for n in v.split()}
files=glob.glob('EraSpec/Contracts/IndexedMerkleTree/**/Properties/*.lean',recursive=True)+glob.glob('EraSpec/Contracts/L2InteropCommitmentTree/**/Properties/*.lean',recursive=True)
found=set()
for f in files:
    s=open(f).read(); o=s
    def sub(m):
        n=m.group(3)
        if n in tag:
            found.add(n); return f'@[{tag[n]}] {m.group(1)}{m.group(2)}{n}'
        return m.group(0)
    s=re.sub(r'(?m)^((?:noncomputable )?(?:def|abbrev) )(Properties\.)(\w+)',sub,s)
    if s!=o:
        if 'import EraSpec.Core.Headline' not in s:
            lines=s.split('\n'); i=max(k for k,l in enumerate(lines) if l.startswith('import '))
            lines.insert(i+1,'import EraSpec.Core.Headline'); s='\n'.join(lines)
        open(f,'w').write(s); print('tagged',f)
print('missing',set(tag)-found)
