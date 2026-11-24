import YM.CF.BProof.Veil.Strong
/-! Trace wallet preserving rotor, root, and reference reading. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Veil
open Function Filter NormedSpace Finset MeasureTheory RecN
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Tape Stint Oasis Scree Palot Wick
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {B m N:Side} {D:GramM N} {j:ℕ}{a b l r c v δ η:ℝ} {P:Spin.Ready j a b l r}{F:Core j a b l r N}{H:Honor P F δ} {p:Pay}
abbrev TokenW(N:Side):=Site (More N) × Seal (Site (More N))
def tArea(i:TokenW N): Seal (Site (More N)):=insert i.1 i.2
lemma t_re (i:TokenW N)(h:i.1∈ i.2): tArea i=i.2:=insert_eq_of_mem h
abbrev Rate (N:Side)(p:Pay)(f:TokenW N→ℝ):Prop:= Moment.Toll Prod.snd f (p.rate/2) (vaultPay p quota)
structure TraceD(H:Honor P F δ)(c v η:ℝ)(p:Pay) where
 ok: Tickets p P δ c v η F H.1
 realT: Ticker (H.1.beam c).st purseT
 biasT: Ticker (Tape.kiln H.1 c v η).st Tape.billR
 imagT: Ticker (Tape.kiln H.1 c v η).st labelR
 realPrice : Rate N p realT.pay
 biasPrice : Rate N p biasT.pay
 imagPrice : Rate N p imagT.pay
lemma trace_d(k:Tickets p P δ c v η F H.1): Nonempty (TraceD H c v η p):= by obtain ⟨b,t,i,V,r,l⟩:= Tape.scroll H k; exact ⟨k,t,b,i,r,V,l⟩
namespace TraceD
-- charge arguments `x` already in native pricing domains; projection to Window for extension
variable (T:TraceD H c v η p)
abbrev Desk (N:Side):= TokenW N ⊕ TokenW N ⊕ TokenW N -- Real Bias Im
abbrev charge (i:Desk N):ℝ:= Sum.elim T.realT.pay (Sum.elim T.biasT.pay T.imagT.pay) i
def proj(i:Desk N): TokenW N:=Sum.elim id (Sum.elim id id) i
def zDesk(i:Desk N):Seal (Site (More N)):=tArea (proj i)
def πReal (x:ℂ): ℂ:= x.re
lemma πReal_norm(x:ℂ): ‖πReal x‖ ≤ ‖x‖:=by unfold πReal; exact (Complex.norm_real _).trans_le (Complex.abs_re_le_norm _)
lemma zen_norm(x:ℂ): ‖Spire.zen x‖≤‖x‖:=by rw [Spire.zen,norm_mul,Complex.norm_I,one_mul,Complex.norm_real]; exact Complex.abs_im_le_norm _
def qReal (i:TokenW N)(x:Loft F δ c v η):ℂ:= πReal (T.realT.line i x.val.1)
def qBias (i:TokenW N)(x: Loft F δ c v η):ℂ:= πReal (T.biasT.line i x)
def qIm (i:TokenW N)(x: Loft F δ c v η):ℂ:= Spire.zen (T.imagT.line i x)
def items := Sum.elim T.qReal (Sum.elim T.qBias T.qIm)
lemma motifPrice : Moment.Toll zDesk T.charge (p.rate/2) (vaultPay p quota+(vaultPay p quota+vaultPay p quota)):=by
 let f:= Prod.snd (α:=Site (More N)) (β:=Seal (Site (More N))); let h:= rearrange f tArea _ (fun i e=> t_re i (T.realT.loc i e).1) _ _ T.realPrice; let v:=rearrange f tArea _ (fun i e=> t_re i (T.biasT.loc i e).1) _ _ T.biasPrice; let p:= rearrange f tArea _ (fun i e=> t_re i (T.imagT.loc i e).1) _ _ T.imagPrice; apply Eq.mp ?_ (Moment.Toll.sum _ _ h _ _ (Moment.Toll.sum _ _ v _ _ p)); congr 1; ext1 (i|(i|i)) <;> rfl -- tune local shadow
lemma shapes(i: Desk N)(u:T.charge i≠0): Grove (terr _) (zDesk i):=by
 rcases i with i|(i|i); · change Grove _ (tArea i); rw [t_re i ((T.realT.loc i u).1),←(H.1.beam c).town]; exact (T.realT.taxes _).conduct u
 · change Grove _ (tArea i); rw [t_re i ((T.biasT.loc i u).1),←(Tape.kiln H.1 c v η).town]; exact (T.biasT.taxes _).conduct u
 change Grove _ (tArea i); rw [t_re i ((T.imagT.loc i u).1),←(Tape.kiln H.1 c v η).town]; exact (T.imagT.taxes _).conduct u
lemma cash(i:Desk N)(x):‖T.items i x‖≤ T.charge i:=by rcases i with i|(i|i); exact (πReal_norm _).trans ((T.realT.taxes i).norms _); exact (πReal_norm _).trans ((T.biasT.taxes i).norms _); exact (zen_norm _).trans ((T.imagT.taxes i).norms _)
lemma visual (u:Occasion c v η)(i:Desk N): ∃ p:Part (window N) (zDesk i) (T.charge i),∀ x,p.val (sion x)=T.items i x:=by
 letI:=standard H u; let L:= H.1.beam c; let A:=T.items i; refine edited (b:=window N) (f:=sion) carol (fun g i=>⟨Oasis.runH H i g,rfl⟩) ?_ (T.motifPrice.nonneg i) (T.cash i) ?_ ?_
 · apply Continuous.measurable; rcases i with i|(i|i); exact Complex.continuous_ofReal.comp (Complex.continuous_re.comp ((T.realT.taxes i).continuousE.comp (continuous_fst.comp continuous_subtype_val))); exact Complex.continuous_ofReal.comp (Complex.continuous_re.comp ((T.biasT.taxes i).continuousE)); exact continuous_const.mul (Complex.continuous_ofReal.comp (Complex.continuous_im.comp (T.imagT.taxes i).continuousE)) -- tune
 · intro x y h; have ht:= stateD H (proj i).2 x y ((window N).onwards h (subset_insert ..)); rcases i with i|(i|i)
   · apply congrArg πReal; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; apply ((T.realT.taxes i).varies ..).trans; rw [show L.st.eval i.2 x.val.1 y.val.1=0 from ht.1,mul_zero]
   · apply congrArg πReal; apply sub_eq_zero.mp; exact norm_le_zero_iff.mp ((T.biasT.taxes i|>.varies x y).trans_eq (by rw [show (Tape.kiln H.1 c v η).st.eval i.2 x y=0 from ht.2,mul_zero]))
   apply congrArg Spire.zen; apply sub_eq_zero.mp; exact norm_le_zero_iff.mp ((T.imagT.taxes i|>.varies x y).trans_eq (by rw [show (Tape.kiln H.1 c v η).st.eval i.2 x y=0 from ht.2,mul_zero]))
 intro g j k h; have hp:k=Oasis.runH H j g:=by rw [← sion_turn H] at h; apply Subtype.ext; let p:=Oasis.runH H j g; obtain ⟨q,r⟩:= Prod.mk.inj h; exact Prod.ext (Subtype.ext (Prod.ext (Subtype.ext (Prod.mk.inj q).1) (Prod.mk.inj q).2)) (Subtype.ext r)
 rw [hp]; rcases i with i|(i|i); exact congrArg πReal ((T.realT.taxes i).gauge g j.val.1); exact congrArg πReal ((T.biasT.taxes i).gauge g j); exact congrArg Spire.zen ((T.imagT.taxes i).gauge g j)
lemma allPeak {D:Type}[TopologicalSpace D](b:Feet N D){A:Raw D (Single N)}(p:Ticker b.st A)(x:D): (∑ i:TokenW N,p.line i x)=(A x).trace:=by rw [fullTrace b.st, Fintype.sum_prod_type]; exact sum_congr rfl fun i _=>(p.book i x).symm
lemma biasPriceX (x)(i:Site (More N)) : ∑ z:Seal (Site (More N)),(T.qBias (i,z) x).re=Tape.bias x i:=by rw [Tape.bias,←peak_same (Tape.kiln H.1 c v η),T.biasT.book, Complex.re_sum]; rfl
lemma totalT(x) : (∑ i:Desk N,T.items i x)=keyF x :=by
 have he:=(T.ok.2.2.2.2 x); rw [he.2]; simp_rw [Desk,Fintype.sum_sum_type,items,Sum.elim_inl, Sum.elim_inr]; change (∑ i,T.qReal i x) + ((∑ i,T.qBias i x)+(∑ i,T.qIm i x))=_; unfold qReal qBias qIm πReal Spire.zen Wick.zen; simp_rw [←mul_sum, ←Complex.ofReal_sum,←Complex.re_sum, ←Complex.im_sum]; rw [allPeak _ T.realT,allPeak _ T.biasT,allPeak _ T.imagT]; push_cast; abel
end TraceD
end YM.CF.BProof.Veil
