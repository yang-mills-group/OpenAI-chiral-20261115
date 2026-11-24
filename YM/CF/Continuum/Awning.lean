import YM.CF.Continuum.Loop
import YM.CF.Continuum.Needle
import YM.CF.Continuum.Tremor
import YM.CF.Nova.Alum

/-! Holonomy localization on four *separate* Polyakov loops with common base,
    and exact probe normalization. Rotate at the common base (measure not fixed).
    This is a finite-volume observable — do not reinterpret on growing tori as
    one common compact-support stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase RG Wilson
open Laurent Next.Free Fir Ember Jill Kea Sods Flare Dial Peaks Cascade Vault Paige
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N : Side}{d:Candle}{x k y:ℝ}{T:Type*}

def chordD (G:Gauge) (u v:G.El):ℝ:= G.chord (u*v⁻¹)
namespace chordD
variable {G:Gauge}
lemma sparse (w a b:G.El): chordD G (w*a) (w*b)=chordD G a b:=by unfold chordD; rw [mul_inv_rev,←mul_assoc,_root_.mul_assoc w a, G.chord_conj]
lemma rightward (w a b:G.El): chordD G (a*w) (b*w)=chordD G a b:=by unfold chordD; congr 1; group
lemma swapP (a b:G.El): chordD G a b=chordD G b a:=by unfold chordD; rw [← G.chord_inv (b*a⁻¹)]; congr 1; group
lemma inverse (a b:G.El): chordD G a⁻¹ b⁻¹=chordD G a b:=by rw [← sparse a]; rw [←rightward b]; simpa using swapP b a
lemma triangle (a b c:G.El): chordD G a c ≤ chordD G a b+chordD G b c:=by unfold chordD; rw [show a*c⁻¹=(a*b⁻¹)*(b*c⁻¹) by group]; exact G.chord_triangle ..
lemma propagate(a b c d:G.El):chordD G (a*b) (c*d) ≤ chordD G a c+chordD G b d:=calc
 _ ≤ chordD G (a*b) (c*b) +chordD G (c*b) (c*d):=triangle ..
 _ = _:= by rw [rightward,sparse]
end chordD

open Tenant
def fourTrace (U : Bkg N) : Axis→ E := yolk U
lemma four_gauge (U:Bkg N)(W:Cart N)(i:Axis): fourTrace (gauge W U) i= W 0*fourTrace U i*(W 0)⁻¹:=by unfold fourTrace yolk; rw [travel_gauge,end_fn]
def axisSites (N : Side) := univ.biUnion (fun i:Axis=> (visits (0:Site N) (cyclic N i)).toFinset)
def axisLoops (N:Side) := leaks (axisSites N)
lemma reads_axes (U V:Bkg N)(h: ∀ i∈axisLoops N,U i=V i) : fourTrace U=fourTrace V:=by
 funext i; unfold fourTrace yolk; apply travel_local; intro e t f; exact h _ (mem_filter.mpr ⟨mem_univ _,mem_biUnion.mpr ⟨_,mem_univ i,List.mem_toFinset.mpr t⟩,mem_biUnion.mpr ⟨_,mem_univ i,List.mem_toFinset.mpr f⟩⟩)

def deviation (U V:Axis→E)(K:E):ℝ:= ∑ i:Axis,chordD group (K*U i*K⁻¹) (V i)
def clampTrace (U V:Axis→E):ℝ:= sInf ((deviation U V) '' Set.univ)
@[fun_prop] private lemma chordContinuity (G: Gauge) {X:Type*} [TopologicalSpace X] {f g:X→G.El} (h:Continuous f)(p:Continuous g):Continuous (fun x=>chordD G (f x) (g x)):= G.continuous_chord.comp (h.mul p.inv)
private lemma devC {X:Type*} [TopologicalSpace X] {f g:X→ Axis→ E} {z: X→ E}(h:Continuous f)(p:Continuous g)(w:Continuous z) : Continuous fun x=> deviation (f x) (g x) (z x):=
 continuous_finsetSum _ fun i _=> chordContinuity group ((w.mul ((continuous_apply i).comp h)).mul w.inv) ((continuous_apply i).comp p)
lemma optimalC (U V:Axis→E):∃ z, clampTrace U V=deviation U V z:=by
 let S:=(deviation U V) '' Set.univ; have he:Continuous (deviation U V):=devC (f:=fun _=> U) (g:=fun _=>V) continuous_const continuous_const continuous_id
 obtain ⟨z,h,r⟩:= (isCompact_univ.image he).sInf_mem (Set.Nonempty.image _ Set.univ_nonempty); exact ⟨z,r.symm⟩
lemma clampTrace_nonneg (U V:Axis→E):0≤clampTrace U V:=by obtain ⟨z,e⟩:=optimalC U V; rw [e]; exact sum_nonneg fun i _=> group.chord_nonneg _
lemma clampTrace_le (U V:Axis→E)(z:E):clampTrace U V≤deviation U V z:=by
 let S:=(deviation U V) '' Set.univ; have he:Continuous (deviation U V):=devC (f:=fun _=> U) (g:=fun _=>V) continuous_const continuous_const continuous_id
 exact csInf_le (isCompact_univ.image he).bddBelow (Set.mem_image_of_mem _ (Set.mem_univ _))
lemma clampTrace_cont (V:Axis→E): Continuous (fun w:Axis→E=> clampTrace w V):=by
 refine isCompact_univ.continuous_sInf ?_
 exact devC (f:=fun x:(Axis→E)×E=> x.1) (g:=fun _=>V) (z:=Prod.snd) continuous_fst continuous_const continuous_snd
set_option maxHeartbeats 300000 in
lemma clampTrace_gauge (U:Bkg N)(V:Axis→E)(g:Cart N): clampTrace (fourTrace (gauge g U)) V=clampTrace (fourTrace U) V:=by
 let S:=fourTrace (gauge g U); let T:=fourTrace U; let h:=g 0
 have he(x:E):deviation S V x=deviation T V (x*h):= sum_congr rfl fun i _=> by
   rw [show S i=h*T i*h⁻¹ from four_gauge U g i]; apply congrArg (fun k:E=> chordD group k (V i)); group
 change sInf ((deviation S V) '' _) = sInf ((deviation T V) '' _)
 apply congrArg sInf
 apply Set.Subset.antisymm
 · rintro t ⟨k,z,q⟩; exact ⟨k*h, Set.mem_univ _,(he k).symm.trans q⟩
 rintro t ⟨k,z,q⟩; exact ⟨k*h⁻¹, Set.mem_univ _, (he _).trans (by rw [inv_mul_cancel_right]; exact q)⟩

def reflectible (N:Side)(k:ℝ)(U:Bkg (More N)):ℝ:= max 0 (1-clampTrace (fourTrace U) (fourTrace (tax (needles N):Bkg (More N))) / k)
lemma reflectible_up(k:ℝ)(U:Bkg (More N)) :0≤ reflectible N k U:= le_max_left ..
lemma reflectible_cost (t:0<k)(U:Bkg (More N)):reflectible N k U≤1:=max_le zero_le_one (sub_le_self _ (div_nonneg (clampTrace_nonneg ..) t.le))
lemma reflectible_where(t:0<k)(U:Bkg (More N))(u:0 < reflectible N k U):∃ x:E,deviation (fourTrace U) (fourTrace (tax (needles N):Bkg (More N))) x<k:=by obtain ⟨x,h⟩:=optimalC (fourTrace U) (fourTrace (tax (needles N):Bkg (More N))); refine ⟨x,?_⟩; unfold reflectible at u; rw [h] at u; exact (div_lt_one t).mp (sub_pos.mp ((lt_max_iff.mp u).resolve_left (lt_irrefl _)))
lemma fourC(N:Side):Continuous (fourTrace (N:=N)):= continuous_pi fun _i=> continuous_travel _ 0
lemma targetC (N:Side)(k:ℝ) : Continuous (reflectible N k):=by
 let P:= fourTrace (tax (needles N): Bkg (More N)); exact continuous_const.max (continuous_const.sub (((clampTrace_cont P).comp (fourC ..)).div_const _))
def compass (N : Side)(k:ℝ) := bosonic N (fun V=>(reflectible N k V:ℂ))
lemma compass_local (k:ℝ) : compass N k ∈ localObs N (axisLoops (More N)) ∅:=by
 refine bosonic_local _ (Complex.continuous_ofReal.comp (targetC ..)) _ ?_ ?_
 · intro x y p; unfold reflectible; simp only [Function.comp_apply]; rw [reads_axes x y p]
 intro t U; unfold reflectible; simp only [Function.comp_apply]; rw [clampTrace_gauge]
lemma compass_star (k:ℝ) (i:Axis) : dagger N i (compass N k) = compass N k:= by unfold compass; rw [dagger_boson]; congr 1; funext i; simp
-- compare frames even with arbitrary root.MyOwn
lemma op_chord : ∃ C:ℝ,0<C∧∀ a b:E,Cube.cmp firstF a b≤ C*chordD group a b:=by
 obtain ⟨C,h,H⟩:= Nova.boundedFrame
 refine ⟨5*C,mul_pos (by norm_num) h,fun a b=>?_⟩; unfold chordD; rw [←cmp_right firstF a b b⁻¹,mul_inv_cancel]; let y:=a*b⁻¹
 refine (le_trans (b:=Fintype.card SU.F*(C*group.chord y)) (cost_D (E:=SU.F) _ (H y) (mul_nonneg h.le (group.chord_nonneg _))) (le_of_eq (by simp [F]; ring)))
lemma fixes_axes (U:Bkg N)(V:E)(d:Candle)(C k t:ℝ)(p:0<C)(t':0<t)(k':0≤k)
    (h:∀ a b:E, Cube.cmp firstF a b ≤ C*chordD group a b)(a: deviation (fourTrace U) (fourTrace (tax d:Bkg N)) V ≤ k) (hp:PlaqBound firstF U t) : ∃ F:Cart N,lawnK (gauge F U) (Kea.tax d) (C*k+400*N.val^2*t):=by
 let Y:=wob N (yolk U); let B:= layout U; let A:=Kea.tax d (N:=N); let D:= layout A; let T:= gauge D A
 let F: Cart N:=fun _=> V
 have hv:lawnK (gauge F Y) T (C*k):=by
   rintro ⟨i,j⟩; unfold T Y A; rw [pacer]; unfold Lattice.gauge wob; split_ifs with h1
   · apply (h _ _).trans; apply mul_le_mul_of_nonneg_left _ p.le; change chordD group (V*yolk U j*V⁻¹) (waveG _^_ ) ≤ _; rw [← tax_peg (N:=N) d j 0]; exact le_trans (single_le_sum (f:=fun i=> chordD group (V*yolk U i * V⁻¹) (yolk A i)) (fun _ _=> group.chord_nonneg _) (mem_univ j)) a
   change cmp _ (V*1*V⁻¹) 1≤_; rw [mul_one, mul_inv_cancel,cmp_id]; positivity
 refine ⟨D⁻¹*F*B,?_⟩; have he:= (Pic.beacon N (gauge F (gauge B U)) (gauge F Y) _ (lawnK.join (fun x=>paleB U t'.le hp x) F) hv).join D⁻¹; unfold T B at *; rw [windy,windy,windy,inv_mul_cancel,windy_u,add_comm _ (C*k)] at he; exact he
lemma towards : ∃ C k:ℝ,0<C ∧0<k∧∀ N:Side,∀ U:Bkg (More N),∀ x t:ℝ,0<x→flags x U=∅→0<t→0<reflectible N t U →∃ F,lawnK (gauge F U) (Kea.tax (needles N)) (C*t+400*(More N).val^2*(k*x)):=by
 obtain ⟨u,v,V⟩:= op_chord; obtain ⟨c,p,H⟩:= Nova.snow_b; refine ⟨u,c,v,p,fun N U x t X g k h=>?_⟩; obtain ⟨l,f⟩:= reflectible_where k U h; exact fixes_axes U l (needles N) _ t _ v (mul_pos p X) k.le V f.le (H (More N) U _ g)
end YM.CF.Window
