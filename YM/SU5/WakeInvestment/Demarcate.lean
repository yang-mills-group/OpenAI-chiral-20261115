import YM.SU5.WakeInvestment.DistancePower
import YM.SU5.WakeInvestment.DivideList
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Ballad.SpinReceipt
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze Cordial
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Lead (Clan)
open Twah
open YM.Stationary (Gaia)
open YM.CF.WakeInvestment
variable {I J K:Type*} {a:ℕ} (G J':List I)(L:List J) (z:I→Clan)(w:J→Clan)
-- reduction by push at suffix.
private lemma c_map1 (x:K)(M:List K)(f:K→Clan)(F:List (Stamp K)→ℂ)(A:List (Stamp K)) : chore f F A (x::M)=∑ i∈ colors (f x), chore f F (A++[(x,i,true),(x,i,false)]) M :=rfl
private lemma c_append (F:List (Stamp I)→ℂ)(A:List (Stamp I)) : chore z F A (G++J')=chore z (fun i=> chore z F i J') A G:=by
 induction G generalizing A with|nil=>rfl|cons i G ih=>rw [List.cons_append,c_map1,c_map1]; exact sum_congr rfl fun i _=>ih _
def stamp (f:I→K) (i:Stamp I) : Stamp K:= (f i.fst,i.snd)
lemma c_map (F:List (Stamp K)→ℂ)(f:I→K)(u:K→Clan)(h:u∘f=z)(A:List (Stamp K))(S: List (Stamp I)) :
    chore u F (A++S.map (stamp f)) (G.map f)=chore z (fun i=> F (A++i.map (stamp f))) S G:=by
 induction G generalizing S with
 | nil=>rfl
 | cons i G ih=>
    rw [List.map_cons,c_map1,c_map1, show u (f i)=z i from congr_fun h i]; apply sum_congr rfl; intro a _; rw [←ih,List.map_append,List.append_assoc]; rfl
private lemma c_mul (k:ℂ)(F:List (Stamp I)→ℂ)(A:List (Stamp I)) : chore z (fun i=>k*F i) A G=k*chore z F A G:=by induction G generalizing A with|nil=>rfl|cons i G ih=>rw [c_map1,c_map1,mul_sum]; exact sum_congr rfl fun i _=> ih _

lemma furnace (z₁:K→Clan) (f:I→K)(g:J→K) (D:Stamp I→Stamp I→ℂ)(E:Stamp J→Stamp J→ℂ)(R:Stamp K→Stamp K→ℂ)(t:∀ i j, R (stamp f i) (stamp f j)=D i j)(p:∀ i j,R (stamp g i) (stamp g j)=E i j)(r:∀ i j,R (stamp f i) (stamp g j)=0):
    chore z₁ (runes R) [] (G.map f++L.map g)=chore (z₁∘f) (runes D) [] G*chore (z₁∘g) (runes E) [] L := by
 let a:= z₁∘f; let b:= z₁∘g; let S:= chore b (runes E) [] L
 have h(A:List (Stamp I))(B:List (Stamp J)): runes R (A.map (stamp f) ++ B.map (stamp g))=runes D A * runes E B:=by
    have he:∀ i∈A.map (stamp f),∀ j∈B.map (stamp g), R i j=0:=by intro i l j h; obtain ⟨i,z,rfl⟩:= List.mem_map.mp l; obtain ⟨j,b,rfl⟩:= List.mem_map.mp h; exact r i j
    rw [rune_divide _ _ _ he,rune_map _ _ _ _ (fun i z=> (p i z).symm),rune_map _ _ _ _ (fun i j=>(t i j).symm)]
 have hv(A:List (Stamp I)):chore z₁ (runes R) (A.map (stamp f)) (L.map g)= S*runes D A:=by
    rw [show A.map (stamp f)=A.map (stamp f) ++ ([]:List (Stamp J)).map (stamp g) from (List.append_nil _).symm,c_map _ b _ g z₁ rfl]; simp_rw [h]; rw [c_mul]; exact mul_comm ..
 rw [c_append,show ([]:List (Stamp K))=[]++([]:List (Stamp I)).map (stamp f) from rfl,c_map _ a _ f z₁ rfl]; simp_rw [List.nil_append,hv]; rw [c_mul]; exact mul_comm .. -- rw empty replacement affects *all* [] but types differ

private lemma negFlow (x:Gaia) : Onyx.pencil (-x)= -Onyx.pencil x:= by
 unfold Onyx.pencil gleamV; simp_rw [norm_neg,PiLp.neg_apply,Complex.ofReal_neg,neg_smul,sum_neg_distrib,mul_neg,smul_neg]
-- exposed read spins use 00 only. general decay from matrix norm or directly curvature formula in K.
abbrev sP (x:I→Gaia)(b:I→DirSpin) := germRho (fun i: Cellz I=> x i.1) b
lemma kP_further (f:ℕ→ Gaia)(p:Tendsto (fun i=>‖f i‖) atTop atTop): Tendsto (fun i=> kP20 (f i)) atTop (𝓝 0):=by
 let x(x:Gaia):= ((x 3:ℂ)+(x 2:ℂ)*Complex.I); let ν(t:ℝ):=(Real.pi^2*t^4)⁻¹
 let C:ℝ:=2*(Real.pi^2)⁻¹
 have he :∀ y:Gaia,‖x y‖≤ 2*‖y‖:=by
    intro y; apply (norm_add_le ..).trans; rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Complex.norm_real,two_mul]; exact add_le_add (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _)
 have h(y:Gaia)(p:0<‖y‖): ‖kP20 y‖ ≤ C*‖y‖⁻¹^3:=by
    unfold kP20 Onyx.pencil; rw [Matrix.smul_apply,quaternion,norm_smul]; change ‖ν ‖y‖‖ * _≤ _; apply (mul_le_mul_of_nonneg_left (he y) (norm_nonneg (ν ‖y‖))).trans_eq; unfold ν C; rw [Real.norm_eq_abs,abs_of_pos (by positivity)]; field_simp
 rw [tendsto_zero_iff_norm_tendsto_zero]; have hp:= (tendsto_inv_atTop_zero (𝕜:=ℝ)).comp p |>.pow 3 |>.const_mul C; rw [zero_pow (by decide), mul_zero] at hp; exact squeeze_zero' (Filter.Eventually.of_forall fun _=> norm_nonneg _) ((p.eventually_gt_atTop 0).mono fun i v=> h (f i) v) hp
-- distance-hypostrophe. On list supports could localize, but since even repeats within i,j okay can pay on full domains of these I,J. D_v in front to have const difference laws including contact. Let layout phases.
lemma spine_primes (u v:I→Gaia)(p:∀ i j,u i-u j=v i-v j)(b:I→DirSpin): sP u b=sP v b:=funext fun ⟨i,x,a⟩=>funext fun ⟨j,y,e⟩=> by unfold sP germRho; rw [show u _ - u _ = _ from p i j]
private lemma same_p{J K:Type*}(T:J→Gaia)(U:K→Gaia)(g:K→J)(x:∀ i,T (g i)=U i)(a b:Stamp K): sP T 0 (stamp g a) (stamp g b)=sP U 0 a b:=by unfold sP germRho; dsimp only [stamp, colbase]; rw [x,x]; rfl
private lemma other_p {A:Type*}(Y:ℕ→A→ Gaia) (x y:Stamp A) (p:Tendsto (fun i=> dist (Y i x.fst) (Y i y.fst)) atTop atTop): Tendsto (fun n=>sP (Y n) 0 x y) atTop (𝓝 0):=by
    obtain ⟨i,a,t⟩:=x; obtain ⟨j,b,u⟩:= y; cases t<;> cases u
    all_goals simp only [sP,funds_neg,dcash,funds] -- rewrite only depending case
    all_goals first| exact tendsto_const_nhds| skip
    · split; next x=>
         change Tendsto (fun n=> -kP20 (Y n j-Y n i)) _ _; have h: Tendsto (fun n=>‖Y n j-Y n i‖) atTop atTop:= p.congr fun n=>by rw [dist_comm,dist_eq_norm]
         simpa using (kP_further _ h).neg
      simp
    · split; next t=> exact kP_further (fun n=> Y n i - Y n j) (by simp_rw [dist_eq_norm] at p; exact p)
      exact tendsto_const_nhds
variable (u:I→Gaia)(v:J→Gaia) (Y:ℕ→I→Gaia)(W:ℕ→J→Gaia)
variable (hp:∀ n i j,Y n i-Y n j=u i-u j) (hz:∀ n i j,W n i-W n j=v i-v j)(hu:∀ i j,Tendsto (fun n=>dist (Y n i) (W n j)) atTop atTop)
local notation "Pβ" => Sum.elim z w
-- only 00 spins in far-factor comparison.
include hp hz hu
set_option maxHeartbeats 350000 in
lemma furthest : Tendsto (fun n=> wakeSum (Sum.elim (Y n) (W n)) (G.map Sum.inl ++ L.map Sum.inr) Pβ 0) atTop (𝓝 (wakeSum u G z 0 * wakeSum v L w 0)):=by
 let X n:= sP (Sum.elim (Y n) (W n)) (0:(I⊕ J)→ DirSpin); let F:=sP u 0; let S:=sP v 0
 let C: Stamp (I⊕ J)→ Stamp (I⊕J)→ℂ:= fun x y=> match x.1,y.1 with| Sum.inl i,Sum.inl j=> F (i,x.2) (j,y.2)|Sum.inr i,Sum.inr j=> S (i,x.2) (j,y.2)|_,_ =>0
 have hr(i j:Stamp (I⊕J)) : Tendsto (fun n=> X n i j) atTop (𝓝 (C i j)):=by
    obtain ⟨i,a⟩:=i; obtain ⟨j,b⟩:=j; cases i<;> cases j
    · next i j=> refine tendsto_const_nhds.congr fun n=> Eq.symm ?_; rw [show X n (Sum.inl i,a) (Sum.inl j,b)=_ from same_p (Sum.elim (Y n) (W n)) (Y n) Sum.inl (fun i=>rfl) (i,a) (j,b), spine_primes _ u (hp n) 0]
    · next i j=> exact other_p (fun n=>Sum.elim (Y n) (W n)) (Sum.inl i,a) (Sum.inr j,b) (hu i j)
    · next i j=> exact other_p (fun n=>Sum.elim (Y n) (W n)) (Sum.inr i,a) (Sum.inl j,b) ((hu j i).congr fun i=> dist_comm ..)
    · next i j=> refine tendsto_const_nhds.congr fun n=> Eq.symm ?_; rw [show X n (Sum.inr i,a) (Sum.inr j,b)=_ from same_p (Sum.elim (Y n) (W n)) (W n) Sum.inr (fun i=>rfl) (i,a) (j,b), spine_primes _ v (hz n) 0]
 let L':=G.map (Sum.inl : I→ I ⊕ J) ++ L.map (Sum.inr : J→I ⊕J)
 have hf:chore Pβ (runes C) [] L' = witness z G (fun p:Cellz I=> u p.1) 0*witness w L (fun p:Cellz J=>v p.1) 0:= furnace G L _ _ _ F S C (fun i j=> rfl) (fun i j=>rfl) (fun i j=>rfl)
 have ht:= (Twah.fulcrum Pβ L' (fun i=>offer_v C X hr i) []).const_mul ((1/2:ℂ)^L'.length); rw [hf,show L'.length=G.length+L.length by unfold L'; simp, pow_add] at ht; unfold wakeSum
 simp only [List.length_append,List.length_map,pow_add]; convert! ht using 2; ring
#print axioms furthest
end YM.CF.Buffered.Ballad.SpinReceipt
