import YM.CF.Onyx.Gold
import YM.CF.Jill.Pine
import YM.CF.Rush.Rill
import YM.CF.Tulip.Metro
import YM.SU5.FiniteGaugeData.Pannier.Veldt
/-! # Fixed-site gap on the flat Spar, all Male, occupancy *within one site*.
From its symbols on the actual AP grid. Doesn't require the spatial translation
invariance of the interacting regulator and doesn't concern scattered momenta
at the cap on a dirty gauge. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Jill Pastry
open Fir Next.Free Bloch
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n N: Side} {G q:ℕ}{j:ℕ}{M:Tulip.Male}
private lemma prilt (x:Site n) (a:Axis) : |pm x a|≤ Real.pi:=abs_le.mpr ⟨(pm_zone x a).1.le,(pm_zone x a).2⟩
private lemma moneyZ (x:Site n): Bound Real.pi (pm x) := (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr (fun i=> prilt x i)
-- integer annulus available each dimension
variable (b:ℕ) (B N:ℕ) -- conflicts N
private lemma ratio_late (N G:ℕ) (p:6≤G)(t:2*G≤N):
 let q:=N/G; 1≤q∧ q ≤ N ∧ q+q+1 ≤ N ∧ (q:ℝ)*G ≤ N ∧ (N:ℝ) ≤ 2*(G:ℝ)*q := by
 let q:=N/G; change 1≤q ∧ _; have hp:0<G:=by omega
 have ht: G*q ≤ N:= Nat.mul_div_le N G -- tune
 have hh:N % G < G:= Nat.mod_lt N hp
 have hf:N%G+G*q=N:= Nat.mod_add_div N G
 have he:1≤q:= (by unfold q; exact (Nat.le_div_iff_mul_le hp).2 (by omega))
 have hl:q≤N:= (Nat.le_mul_of_pos_left _ hp).trans ht
 have hv:q*6 ≤ G*q:=by rw [mul_comm G]; gcongr
 refine ⟨he,hl,by omega,by rw [mul_comm]; exact_mod_cast ht,?_⟩
 exact_mod_cast (show N≤ 2*G*q by nlinarith)

private lemma frame_pm (x:ℕ)(p:6≤G) (t:2*G ≤ n.val)(l:n.val/G≤x)(u:x<n.val/G + n.val/G): Real.pi/G ≤ Lat.principal (x:Per n) ∧ Lat.principal (x:Per n) ≤ 5*Real.pi/G:= by
 obtain ⟨hp,hl,hv,hq,hN⟩:=ratio_late n.val G p t
 let y:= Lat.winding (x:Per n); have ht:(0:ℝ)<G:=by exact_mod_cast (show 0<G by omega)
 have z:0<(n.val:ℝ):= nPos n
 let N:= n.val; let q:= n.val/G
 rw [Lat.principal]
 have hh: Real.pi/G ≤ y ∧ y≤5*Real.pi/G:=by
    unfold y Lat.winding; rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le u (by omega))];
    have hx:(q:ℝ)≤x:=by exact_mod_cast l
    have heμ:(x:ℝ) ≤ 2*(q:ℝ):=by exact_mod_cast (show x≤2*q by change x<q+q at u; omega)
    have v: (1:ℝ)≤q:=by exact_mod_cast hp
    have hGp : Real.pi>0:= Real.pi_pos
    change (n.val:ℝ) ≤ 2*(G:ℝ)*q at hN; change (q:ℝ)*G ≤ _ at hq
    rw [show Real.pi/G=(1/(G:ℝ))*Real.pi by ring,show 5*Real.pi/G = (5/(G:ℝ))*Real.pi by ring]
    constructor
    · apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le; rw [div_le_div_iff₀ ht z]; nlinarith
    apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le; rw [div_le_div_iff₀ z ht]; nlinarith
 rw [if_pos (hh.2.trans (show 5*Real.pi/G≤ Real.pi from (div_le_iff₀ ht).2 (by nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_right (show (5:ℝ)≤G by exact_mod_cast (le_trans (by decide:5≤6) p)) Real.pi_pos.le])))]
 exact hh
private lemma nonempty_band (p:6≤G)(t:2*G≤n.val): ∃ k: Finset (Site n),  (n.val:ℝ)^4 ≤ (2*(G:ℝ))^4*(k.card:ℝ) ∧ ∀ x∈k, Real.pi/G ≤ ‖pm x‖ ∧ ‖pm x‖ ≤ 5*Real.pi/G:=by
 classical
 let q:= n.val/G
 obtain ⟨hq,h₀,hg,hV,hf⟩:=ratio_late n.val G p t
 let F:= Axis→Fin q; let f(x:F)(i:Axis):Per n:= ((q+(x i).val:ℕ):Per n)
 have H(x:Fin q):q+x.val<n.val:=by change q+q+_ ≤ _ at hg; have he:=x.isLt; omega
 let S:Finset (Site n):= univ.image f
 have he: S.card=q^4:= by
    unfold S; rw [Finset.card_image_of_injective _ (show Injective f from (fun x y h=> by funext i; have ht:((q+(x i).val:ℕ):Per n)= ((q+(y i).val:ℕ):Per n):= congrFun h i; have hr := congrArg ZMod.val ht; rw [ZMod.val_natCast_of_lt (H _), ZMod.val_natCast_of_lt (H _)] at hr; exact Fin.ext (Nat.add_left_cancel hr))),card_univ, Fintype.card_fun]; simp [Axis] -- tune
 refine ⟨S,?_,?_⟩; · rw [he,Nat.cast_pow,← mul_pow]; exact pow_le_pow_left₀ z_nonneg hf 4 -- tune
 intro x hx; obtain ⟨y,_,rfl⟩:= mem_image.mp hx
 let W:= pm (show Site n from f y); have hv(i): Real.pi/(G:ℝ) ≤ W i ∧ W i ≤ 5*Real.pi/G:= frame_pm (q+(y i).val) p t (Nat.le_add_right ..) (Nat.add_lt_add_left (y i).isLt q)
 refine ⟨le_trans ((hv 0).1.trans (le_abs_self _)) (norm_le_pi_norm W 0), (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun i=> by change |W i| ≤_; rw [abs_of_nonneg ((show 0 ≤ Real.pi/(G:ℝ) by positivity).trans (hv i).1)]; exact (hv i).2)⟩
where z_nonneg: (0:ℝ)≤ n.val:=Nat.cast_nonneg _
open WilsonFrame
private abbrev disk' (j:ℕ)(M:Tulip.Male)(i:SpinIdx)(x:Site n) := if i∈ plusHalf then disk j M (pm x) else 1-disk j M (pm x)
private lemma milk (y:Site n): mel y ∈ realCube zone:= base_subset_realCube zone_pos (mel_h _)
private lemma foxy_s (M:Tulip.Male)(j:ℕ)(p:Site n): let P:=mel p; bar j M.val (mel (backN p))+ bar j M.val P = (2:ℂ) • ((1/2:ℂ) • 1 + (shell j M.val P-1/2) • grading) := by
 obtain ⟨w,h⟩:= dollar p; intro P; change mel (backN p)= -P + reciprocal w at h; have hx:P∈realCube zone:= milk _; have hg: -P∈realCube zone:=realCube_neg hx; rw [h,bar_overlap j M.val hg w (h ▸ milk _),bar,skin_mix j M.val hg,Onyx.foxy j M hx hg, mix_neg j M.val M.property P]
 -- find zen neg
 unfold bar; rw [smul_neg, ← skin_mix j M.val hx, ← neg_one_smul ℂ (skin j M.val P), zenS,neg_one_smul,mul_neg]; module
private lemma disk_barSum (M:Tulip.Male)(j:ℕ)(x:Site n)(a b:SpinIdx):
    bar j M.val (mel (backN x)) a b + bar j M.val (mel x) a b = if a=b then (2:ℂ)*↑(disk' j M a x) else 0:=by
 rw [← Matrix.add_apply,foxy_s]; rw [ordA,Adef.trans raising.symm,show shell j M.val (mel x)=(disk j M (pm x):ℂ) from Jill.express j (pm x) M.val (milk x) M.property] -- express pattern maybe cast
 simp only [disk',disk,Matrix.add_apply,Matrix.smul_apply, Matrix.sub_apply, Pi.smul_apply,smul_eq_mul, cutM, Matrix.one_apply]; split_ifs with h g <;> try subst b <;> simp [*,one_div] <;> try ring
 all_goals simp [*]

private lemma weigh_z (x y:Site n) (z:ℂ) : Fourier n x y * z * star (Fourier n x y)= ((n.val:ℂ)^4)⁻¹ * z := by
 unfold Fourier Lat.normF; simp only [Matrix.of_apply,star_div₀,star_pow,star_natCast]; rw [show _*z*_= (star (Lat.frequency y x)*Lat.frequency y x)*z/((n.val:ℂ)^4) from ?_,Lat.frequency_unit]; rw [div_eq_mul_inv,one_mul,mul_comm];
 · ring
private lemma milk_ratio (N:Side)(j:ℕ)(t:Site N)(h:1≤j)(M:Tulip.Male)(a b:SpinIdx) :
    Rush.plates N (bar j M.val) (t,a) (t,b)= if a=b then (((N.val:ℂ)^4)⁻¹)*(↑(∑ x:Site N,disk' j M a x):ℂ) else 0:=by
 rw [Rush.price]; let f:=((N.val:ℂ)^4)⁻¹; let z(x:Site N):=bar j M.val (mel x) a b; simp_rw [weigh_z]
 let D(x:Site N):= if a=b then (2:ℂ)* ↑(disk' j M a x) else 0
 change ∑ i,f*z i = if a=b then f * _ else _; rw [←mul_sum]
 have hp : (∑ i:Site N,D i)=(2:ℂ)* (∑ i,z i):=by
    simp_rw [D,← disk_barSum]; change (∑ i:Site N,(z (backN i)+z i))=_; rw [sum_add_distrib,Equiv.sum_comp]; ring
 by_cases e:a=b
 · unfold D at hp; simp only [if_pos e,←mul_sum (s:=univ),← Complex.ofReal_sum] at hp
   rw [if_pos e, mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0) hp.symm]
 unfold D at hp; simp [e] at hp ⊢; exact Or.inr hp

-- real numbers securely on belt. heart upper.
private lemma dollar_m (M:Tulip.Male)(i:Site n): 0≤disk j M (pm i) ∧ disk j M (pm i) ≤ 1:=by
 let V:=tmap (pm i); have hp:= milk i
 let z:= mixL j M.val V
 have he:0 ≤ ∑ x:Axis,(z x).re^2 :=sum_nonneg fun i _=> sq_nonneg _
 refine ⟨norm_nonneg _,?_⟩
 change ‖shell j M.val (mel i)‖ ≤ 1; rw [shell_inv _ _ hp (mel_away i), prodM_self _ (phys_mix j M.val M.property _ hp.1)]; let A:=∑ x:Axis,(z x).re^2; change ‖((1:ℂ)+(A:ℂ))⁻¹‖≤1; rw [← Complex.ofReal_one,← Complex.ofReal_add,← Complex.ofReal_inv,Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr ?_),inv_eq_one_div]; swap; · linarith only [show 0≤A from he]
 change _≤ (1:ℝ); exact (div_le_one (by have := show 0≤A from he; positivity)).mpr (le_add_of_nonneg_right he)
private def copper (T c:ℝ) (H G:ℕ):= min (c*(Real.pi/G)^2) (1/2)
private lemma chooses (T:ℝ)(h:0<T):∃ G≥ (6:ℕ), T*(5*Real.pi/G)^2 ≤ (1/2:ℝ):=by
 have ht:Tendsto (fun k:ℕ=> T*(5*Real.pi/(k:ℝ))^2) atTop (𝓝 0):=by
    simp_rw [div_eq_mul_inv]; simpa only [Function.comp_apply,mul_zero,zero_pow (by decide: (2:ℕ)≠0)] using ((((tendsto_inv_atTop_zero (𝕜:=ℝ) |>.comp tendsto_natCast_atTop_atTop).const_mul (5*Real.pi)).pow 2).const_mul T)
 exact ((eventually_ge_atTop 6).and (ht.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2)))).exists
private lemma milkPrice (Z:ℝ)(hZ:0 ≤ Z)(X:Site n→ℝ) (q:∀ i,0 ≤ X i) (S:Finset (Site n)) (p:∀ i∈S, Z ≤ X i)(t:(n.val:ℝ)^4 ≤ (2*(G:ℝ))^4*(S.card:ℝ)) (hg:0<G) :
    Z/(2*(G:ℝ))^4 ≤ ((n.val:ℝ)^4)⁻¹ * ∑ i,X i:=by
 let V:= (n.val:ℝ)^4; let L:=(2*(G:ℝ))^4; have H:0<V:=by unfold V; positivity
 have ℓ:0<L:=by unfold L; positivity
 have hK: (S.card:ℝ)*Z ≤ ∑ i,X i:= (le_trans (by simp [nsmul_eq_mul] : (S.card:ℝ)*Z ≤ ∑ _∈S,Z) (sum_le_sum p)).trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> q i))
 change Z/L ≤ V⁻¹*_ ; rw [mul_comm V⁻¹, ←div_eq_mul_inv,div_le_div_iff₀ ℓ H]
 nlinarith only [mul_le_mul_of_nonneg_left hK ℓ.le,mul_le_mul_of_nonneg_left (show V≤L*S.card from t) hZ]
private def totalDisk (n:Side)(j:ℕ)(M:Tulip.Male)(a:SpinIdx):= ((n.val:ℝ)^4)⁻¹ * ∑ i:Site n,disk' j M a i
private lemma bothValues (j:ℕ)(h:1≤j): ∃ Z> (0:ℝ),∃ N:ℕ,∀ n:Side,N ≤ n.val → ∀ M:Tulip.Male,∀ a:SpinIdx,
   Z ≤ totalDisk n j M a ∧ totalDisk n j M a ≤ 1-Z:=by
 obtain ⟨c,T,hc,hT,t⟩:= Jill.zip h
 obtain ⟨G,hg,u⟩:= chooses T hT
 let L:=(2*(G:ℝ))^4; let Z:=min (c*(Real.pi/G)^2) (1/2); have hp:0<G:=by omega
 have hZ:0<Z:=lt_min (by positivity) (by norm_num)
 refine ⟨Z/L, div_pos hZ (by unfold L; positivity),2*G,fun n t₀ M a=>?_⟩
 obtain ⟨S,d,v⟩:= nonempty_band hg t₀
 let Y(i:Site n):=disk' j M a i
 have height(i:Site n):0≤ Y i ∧ 0 ≤ 1-Y i:=by obtain ⟨p,q⟩:= dollar_m (j:=j) M i; unfold Y disk'; split <;> constructor<;> linarith
 have hx (i:Site n)(y:i∈ S):Z ≤ Y i ∧ Z ≤ 1-Y i:=by
    obtain ⟨a0,a1⟩:=t M (pm i) (moneyZ ..); obtain ⟨j0,j1⟩:=v i y; have hp:c*(Real.pi/G)^2 ≤ disk j M (pm i):= a0.trans' (by gcongr); have ht: disk j M (pm i)≤ 1/2:= (a1.trans (by gcongr)).trans u; unfold Y disk'; have he:Z≤(1/2:ℝ):=min_le_right ..; split <;> constructor <;> linarith [show Z≤ c*(Real.pi/G)^2 from min_le_left ..]
 constructor
 · exact milkPrice Z hZ.le Y (fun i=> (height i).1) S (fun i w=>(hx i w).1) d hp
 let F:=((n.val:ℝ)^4)
 have ht: F*(F)⁻¹=1:= mul_inv_cancel₀ (by unfold F; positivity)
 have hu:= milkPrice Z hZ.le (fun i=> 1-Y i) (fun i=>(height i).2) S (fun i v=>(hx i v).2) d hp
 rw [sum_sub_distrib,sum_const,card_univ, site_card, nsmul_eq_mul,Nat.cast_pow,mul_one] at hu
 change _ ≤ F⁻¹*(F-_) at hu; change F⁻¹*∑ i,Y i ≤1-Z/L; change (Z/L)≤ _ at hu
 linarith

lemma flat_formula (j:ℕ)(u:1≤j)(M:Tulip.Male) (x:Site n)(a b:SpinIdx)(p q:SU.Slot): Dial.spar j M (1:Skye.Pane n) ((x,a),p) ((x,b),q) = if a=b ∧ p=q then (totalDisk n j M a:ℂ) else 0:= by
 rw [Dial.spar,profile_trivial,Tulip.funde_flat j u M,show cart n (tub (bar j M.val))= plates n (bar j M.val) from cart_traded (cBar j M.val true u M.property) n, Matrix.kronecker_apply]
 -- rewrite Milk
 rw [milk_ratio n j x u M a b]
 by_cases h:a=b<;>by_cases z:p=q <;> simp [totalDisk,h,z,Matrix.one_apply]
 split_ifs <;> push_cast <;> rfl
/-- Uniform BOTH orientations and all colors all Singer sites. -/
lemma kidney (j:ℕ)(h:1≤j): ∃ z> (0:ℝ), ∃ N:ℕ, ∀ n:Side,N ≤ n.val → ∀ (M:Tulip.Male)(b:Bool),
    let P:=hand b (Dial.spar j M (1:Skye.Pane n))
    (∀ i:Single n, ∃ d:ℝ, z≤d ∧ d≤1-z ∧ P i i=(d:ℂ)) ∧ ∀ i k:Single n,i.1.1=k.1.1→i≠k→P i k=0 := by
 obtain ⟨z,hz,N,t⟩:= bothValues j h
 refine ⟨z,hz,N,fun n u M b=> ⟨?_,?_⟩⟩
 · rintro ⟨⟨x,i⟩,p⟩
   obtain ⟨hp,ht⟩:= t n u M i; cases b; · exact ⟨totalDisk ..,hp,ht,by simpa [hand] using flat_formula j h M x i i p p⟩
   exact ⟨1-totalDisk n j M i,by linarith,by linarith,by rw [hand,if_pos rfl,Matrix.sub_apply, Matrix.one_apply_eq,flat_formula j h]; simp⟩
 rintro ⟨⟨x,i⟩,p⟩ ⟨⟨y,j'⟩,q⟩ (rfl: x=y) a; have he: ¬(i=j' ∧ p=q):=by rintro ⟨rfl,rfl⟩; contradiction; -- tune
 cases b; exact (flat_formula j h _ _ _ _ _ _).trans (if_neg he)
 unfold hand; rw [if_pos rfl,Matrix.sub_apply,Matrix.one_apply_ne a,flat_formula j h, if_neg he,sub_zero]
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.kidney
