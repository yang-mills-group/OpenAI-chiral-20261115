import YM.CF.Slate.Rift
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Slate
open Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
open AnalyticBridge.GaussianFieldAlignment
local notation "G"=> SU.group
variable {K:Teller SU.group} {T:Tube SU.group S}
local notation "C"=>bareStores S
lemma bumpBill {k:S.Choices}(t:ℝ)(V:Config G c)(he:K.Funds S T)(i:Slots S)(a:Fish (Key F G))(Y:LinkArray G (Frozen (bareStores S) x F)): wheel (bareStores S) F T x k q t Y (leaveX F x a) V i= if keep x (shots S x) (bareStores S) F i then Rows.slip • (Offset.fixedBase T x V k i+ bump T x V k (meal F x a) i) else 0:=by
 have ht:Rows.input x C F (autoShell q t V Y)=0:=by
    funext z; unfold Rows.input; split
    next h =>
       split
       next l => exact False.elim ((notChilled S F x ⟨z,h⟩) l)
       rfl
    rfl
 obtain ⟨A,B,h,H⟩:=he.feeds; unfold wheel axle; rw [Rows.moved T x V k _ _ _ h, Offset.f0,ht,van_g he,add_zero]; rw [add_comm]; rw [← show ∀ z y:LogArray SU.group (Slots S), tape.symm (z+y)=(tape.symm z)+tape.symm y from fun z y=>Next.SectorChange.colors.symm.map_add z y]; change tape (tape.symm _) _=_; rw [tape.apply_symm_apply]; unfold selected Rows.restrict; simp only [Pi.add_apply]; split <;> simp only [smul_add,add_zero]; rfl
lemma skipBill {V:Config G c}{k:S.Choices}(he:K.Funds S T)(i: Slots S)(a:Ark T F)(p:¬keep x (shots S x) (bareStores S) F i): gloss T x F k i a=0:=by
 obtain ⟨s,y⟩:=i; unfold gloss pill dragB; change bump T x _ _ (trays S x F a.2) _= _; exact skip_bump T _ _ _ (bareStores S) F s y _ (funds_branch he) p
lemma tickE (K:Teller SU.group)(F:Forest S.ratio)(h:K.Funds S T)(k:S.Choices)(u:Mast G c)(v: Fish (Key F G))(q:Chi)(d:ℝ)(i:Slots S)(l:ℕ):
 let Y := (1:LinkArray G (Frozen (bareStores S) x F)); let U:=facadeX G u; let z:= Newt.sol S T k x F l u; let g(s:Fish (Key F G)):= media i (wheel (bareStores S) F T x k q d Y (leaveX F x s) U)
 g (v+z)-g z= ‖gloss T x F k i (u,v)‖^2/2 - OreK T x F k l i (u,v):=by
 intro Y U z g; by_cases l:keep x (shots S x) C F i
 swap
 · unfold g media; rw [bumpBill d U h, bumpBill d U h,if_neg l,if_neg l, skipBill (V:=U) h i (u,v) l]; unfold OreK; rw [skipBill (V:=U) h i (u,v) l]; simp
 unfold g media; rw [bumpBill d U h, bumpBill d U h, if_pos l,if_pos l, inv_smul_smul₀ Rows.slip_pos.ne',inv_smul_smul₀ Rows.slip_pos.ne']
 let A:= Offset.fixedBase T x U k i; let f:=gloss T x F k i; obtain ⟨c,v',H,hY⟩:=h.feeds
 let X:= f (u,z); let N:= f (u,v); have hy: bump T x U k (meal F x (v+z)) i=N+ X:=by rw [map_add,bump_add T x U k H]; rfl
 rw [hy]; change ‖A+(N+X)‖^2/2- ‖A+X‖^2/2=_ - (-inner ℝ (A+X) N); rw [show A+(N+X)= (A+X)+N by abel,norm_add_sq_real]; ring_nf; rfl -- tune
lemma landed_exit (u:Config G c)(a:Fish (Key F G)):landed x (bareStores S) F u (1:LinkArray _ _) (leaveX F x a)=increment (replica S.ratio u) (meal F x a):=by
 ext1 i; by_cases h:i∈ F.trunks
 · change landed _ _ _ _ _ _ _= increment _ (trays S x F a) _; have hp: replica S.ratio u i=1:= if_pos (F.trunk_internal h); unfold landed Next.SectorChange.physical; rw [F.on_tree _ ⟨i,h⟩,increment,hp,trays,fresh,dif_neg (not_not.mpr h),SU.group.mat_lieExp_zero,mul_one]
 let j: F.Free:= ⟨i,h⟩; let p:Active C x F:=⟨j,notChilled S F x j⟩; unfold landed Next.SectorChange.physical; change F.drape _ p.val.val= _; rw [F.off_tree]; unfold Next.SectorChange.returned thaw; rw [freeze_regular]; unfold release increment; rw [show meal F x a i=tape (leaveX F x a) p from Gap.freshly_read C F (shots S x) _ p]
end YM.CF.Slate
