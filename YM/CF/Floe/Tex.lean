import YM.CF.Floe.Oyster
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
open Jet Phase.Sample MeasureTheory
open scoped ContDiff
variable{K b c d r R A C e d₁ d₂ v:ℝ}
variable {m B N:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{n:ℕ}
private def deΦ : ℂ→L[ℝ]ℂ:=((4:ℝ)⁻¹) • Complex.ofRealCLM.comp Complex.reCLM
private def imΦ : ℂ→L[ℝ]ℂ:=Complex.I • Complex.ofRealCLM.comp Complex.imCLM
lemma honors_F (n:ℕ)(p:1≤K)(l:0<R)(B:Side):∃ a b d e:ℝ, 0 ≤ a∧0≤ b∧0≤ d∧0≤e∧ ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](q:ℝ)(D:Room B q)(m:Side)(v:Part m B)(Y:Scroll m B v) (x:Stamp m B)(V:E→Pack m B)(S:Set E),IsOpen S → Tagged q K n V S → ∀ y∈ S, ∀ (C L:ℝ),GripK Y R C L →∀ (w:Hub m), sanctioned m B x w → Allows n (fun z=> Y.value x w (V z)) y ((d*Y.mint x)+ mercury (chairs m B x).card n a (mercury (chairs m B x).card n b (e*Y.mint x))):=by
 obtain ⟨A,u,h⟩:=ryth n K B p; obtain ⟨C,v,P⟩:=rock_v n K p B; obtain ⟨Z,w,Rp⟩:= brimA n l p B; obtain ⟨Y,hq,G⟩:=glowF p l B n
 refine ⟨A,C,‖deΦ‖*Z,‖imΦ‖*Y,u,v,by positivity,by positivity,fun E _ _ _ q D m κ T x V S he H y yp c L g t z=>?_⟩; have hx :=h m E S he (fun z=>(V z).1) (fun i z=> (H i z).2.1)
 obtain ⟨F,J,ht,hV,W,Q,hG⟩:=g.ext l; let Hx:= chairs m B x; let U:= inks m B (T.phi x) t; let d:= T.dull x; let z':=T.din x; have hd:= (hG.stamped x).posT; have hp: 1 ≤ way B:= by unfold way; omega
 have hk: d ≤ T.mint x ∧ z'≤ T.mint x:= ⟨le_add_of_nonneg_right (mul_nonneg (by positivity) hd),le_trans (le_mul_of_one_le_left hd (by exact_mod_cast hp)) (le_add_of_nonneg_left (Q.stamped x).posT)⟩
 have hu : Allows n (fun z=> coastal m B U (V z)) y (mercury Hx.card n A (mercury Hx.card n C (Y*T.mint x))) :=by
    refine merit_F x V S y H he yp hx (fun S v f u=> P m E S v V (fun _=>f) (fun i e=>⟨(H i (u e)).2.1,(H i (u e)).2.2,voteR f p i⟩)) t z (T.phi x) (g.meter.t2.stamped x) D (mul_nonneg hq (hd.trans hk.2)) ?_; intro i k r v e; rw [hV]; exact G E m (J x) (W x).2 (hG.stamped x).continuousE (T.mint x) (fun i=>((hG.stamped x).norms i).trans hk.2) V _ _ r q D e ⟨(H r v).2.1,(H r v).2.2,voteR _ p _,voteR _ p _⟩ t
 have hw: Allows n (fun i=> deΦ (accessK m B (stick 0) (stick 0) t (V i).1 (slot m (V i).2) (T.hull x))) y (‖deΦ‖*Z*T.mint x):=by
    rw [mul_assoc,ht]; apply Allows.linear deΦ _ le_rfl; have hv:= stick_in (0:Row) (mem_singleton_self _); have hb: ‖stick (0:Row)-stick 0‖ ≤ 2/(way B:ℝ):=by rw [sub_self,norm_zero]; positivity
    exact Rp E m (F x) (W x).1 (Q.stamped x).continuousE _ (fun i=> ((Q.stamped x).norms i).trans hk.1) _ _ _ _ t y q {(0:Row)} hv hv hb D (H y yp).2.1 (fun i=>(H y yp).2.2 i.1) ((show ∀ᶠ i in 𝓝 y,i∈ S from he.mem_nhds yp).mono (fun i v=> ⟨(H i v).1.1,(H i v).1.2⟩)) -- failure mem_nhds .mono
 have he(x:ℂ):deΦ x=hsun x ∧ imΦ x=sideS x:=by simp [deΦ,hsun,imΦ,sideS,Complex.real_smul,div_eq_mul_inv, mul_comm]
 have h0:=hu.linear imΦ le_rfl; simp_rw [(fun x=> (he x).1)] at hw; simp_rw [(fun x=>(he x).2)] at h0; apply (hw.add h0).mono; refine add_le_add le_rfl (le_of_eq ?_); unfold mercury Hx; ring
end YM.CF.Floe
