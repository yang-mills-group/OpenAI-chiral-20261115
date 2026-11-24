import YM.CF.Arena.Reel
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Matrix
section norm
variable {I: Type}[Fintype I] [Nonempty I]
lemma arP(A:ℝ) : ‖(Fintype.card I:ℂ)⁻¹‖*((univ:Finset I).card*A)= A:=by rw [norm_inv,Complex.norm_natCast,card_univ,←mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]
lemma V_as(p:Support c)(f:I→Site c→SpaceX G c): (∑ i∈p, aria fun U:I=>f U i)= aria (fun i=>∑ j∈p,f i j):=by unfold aria; rw [←smul_sum,sum_comm]
lemma V_aa(f g:I→SpaceX G c): aria (f+g)= aria f+aria g:=by unfold aria; simp only [Pi.add_apply,sum_add_distrib,smul_add]
lemma V_seq (X:SpaceX G c): aria (fun _:I=>X)=X:=by unfold aria; simp only [sum_const,card_univ]; ext i; simp only [Pi.smul_apply]; change _* (Fintype.card I • X i)= X i; simp
lemma voyage {A':ℝ}(F:I→FileM c G)(r:ℕ)(p:∀ v:I, Prox (F v) r A')(h:∀ v:I,∀ i, ContDiffAt ℝ (r:ℕ∞ω) (satX (F v i)) 0):Prox (fun i=>aria (fun v:I=>F v i)) r A':=by
 intro i s; let V:Fin r→InputZ G c:=fun j=> flaw G (i j) (s j); let t:ℂ:=(Fintype.card I:ℂ)⁻¹; let P(i):= aria (fun v:I=> F v i); let Q(v:I):=∑ i, cake r (satX (F v i)) V; have hp(i:Site c): cake r (satX (P i)) V=t* (∑ v,cake r (satX (F v i)) V):=by
    unfold P aria; rw [cake_ch  _ (by simp_rw [satX,Function.comp_def,Finset.sum_apply]; exact ContDiffAt.sum (fun v _=>h v i)), cakeSum (fun v=>F v i) (fun v=>h v i) V] -- tune args
 change ‖∑ i,cake r (satX (P i)) V‖ ≤ _; simp_rw [hp]; rw [←mul_sum,sum_comm]; apply (norm_mul ..).le.trans; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (norm_nonneg t)).trans (?_)
 apply le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (g:=fun _=>A') fun j _=>p j i s) (norm_nonneg t)); rw [Finset.sum_const,nsmul_eq_mul]; exact (arP _).le
lemma urgeM {v:Site c}{r k j n:ℕ}{A D:ℝ}(P:I→SpaceX G c)(H:∀ i:I, Urge (P i) v j k r n σ A D)(hp:0<σ)(hj:j ≤ n)(hk:k ≤ n): Urge (aria P) v j k r n σ A D:= by apply Urge.under ((urgeSum (univ:Finset I) (fun i _=> H i) hp hj hk).change hp hj hk ((Fintype.card I:ℂ)⁻¹)) _ _ le_rfl; exact (arP A).le; exact (arP D).le
end norm
local instance : Nonempty (Tab S):=⟨⟨Classical.choice (Tree.select _ S.patch.odd_side),Classical.ofNonempty⟩⟩
variable {o:Site c}{a C:ℝ}{r:ℕ}{F:Tab S→FileM c G}{Z:Site c→ Support c}{Y:Tab S}
def zig (F:Tab S→FileM c G)(Y:Tab S)(Z:Site c→Support c)(i j:Site c):= aria (fun v:Tab S=> twitch F Y v Z j i)
lemma zig_p (h:∀ g k,∀ v,Kind S g k (pavilion r v)→ F g v=F k v)(i j:Site c)(p:separation j i>r) : zig F Y Z i j=0:=by
 rw [show zig F Y Z i j=aria (fun _ : Tab S => 0) from ?_, V_seq]; unfold zig; apply congrArg aria; funext V; exact twitch_z F _ _ _ h j i ((theatre ..).not.mpr p.not_ge)
lemma zig_sum (p:∀ g:Support c→SpaceX G c, (∑ i,(g (insert i (Z i))-g (Z i)))=g univ-g ∅)(i:Site c): F Y i=aria (fun u:Tab S=> F u i)+ ∑ j, zig F Y Z i j:=by
 have hp(u:Tab S): (∑ j,twitch F Y u Z j i)=F Y i-F u i:=by simpa only [twitch,all_U,empty_U] using p (fun X=> F (unite S X Y u) i)
 unfold zig; rw [V_as]; change F Y i= aria (fun v:Tab S=>F v i)+aria _; rw [← V_aa]; symm; refine _root_.Eq.trans (congrArg (aria (I:=Tab S)) ?_) (V_seq (I:=Tab S) _); funext v; simp only [Pi.add_apply,hp,add_sub_cancel] -- tune
lemma zig_tot (i:Site c)(h:∀ g k,∀ v,Kind S g k (pavilion r v)→ F g v=F k v): (∑ j,zig F Y Z j i)= aria (fun v:Tab S=> imp F Y v Z r i):=by simp_rw [impU _ _ _ _ h]; unfold zig; rw [V_as]
lemma zig_U(i j:Site c){r k t:ℕ}(h:∀ v p, Urge (F v p) p k t r n σ C D)(ht:k ≤n)(hr:t ≤ n)(hx:0<σ): Urge (zig F Y Z i j) i k t r n σ (C+C) (D+D):=by
 apply urgeM _ (hp:=hx) (hj:=ht) (hk:=hr); intro v; apply Urge.under (p:=_) (l:=r) _ le_rfl le_rfl le_rfl -- tune
 let P:= F (unite S (insert j (Z j)) Y v) i; let Q:=F (unite S (Z j) Y v) i
 have he: Urge ((-1:ℂ) • Q) i k t r n σ C D:= by simpa using (h _ i).change hx ht hr (-1) -- target -1 smul
 change Urge (P-Q) _ _ _ _ _ _ _ _; rw [show P-Q=P+(-1:ℂ) • Q from by simp [sub_eq_add_neg]]; exact urge_add _ _ (h _ _) he hx ht hr
lemma boardS(i j:Site c){A B: Tab S}(h:∀ g k,∀ i,Kind S g k (pavilion r i)→ F g i=F k i)(p:Kind S A B (pavilion r i)): zig F A Z i j=zig F B Z i j:=by unfold zig twitch; apply congrArg aria; funext u; rw [h _ (unite S _ B u) i (differT p u),h (unite S _ A u) _ i (differT p u)]
end YM.CF.Arena
