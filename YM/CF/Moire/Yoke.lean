import YM.CF.Moire.Gilt
/-! Extensive *nonperturbative* analytically tilted Weyl sea. Projection complexification with gauge for sector extensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Moire
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire Branch Nacre
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m:ℕ}{n:Side}
variable {b d e w r:ℝ}{S:Seal (Site (More n))}
abbrev Rota(m:ℕ)(n:Side):= HopK n× HopK n×Trip m n
def pays(x y:HopK n)(i: Trip m n):ℝ:=8*(1+notx m (x,Classical.ofNonempty) (y,Classical.ofNonempty) i)
def bend(a:Shape)(x:HopK n)(v:PrizeX n):= traceP (east a x) (rayW a (boot (terse x) v))∪ traceP (east a x) (reverse (rayW a (boot (terse x) v)))
def Beam(a:Shape)(x y:HopK n):= traceP (east a x) (rayW a (shiftH (terse x) (terse y)))
def Ferry(a:Shape)(x y: HopK n)(j:Trip m n): Seal (Site (More n)):= Beam a x y ∪ univ.biUnion (fun i=>bend a x (j i))
lemma bend_G(a:Shape)(x: HopK n)(v:PrizeX n): east a x∈ bend a x v ∧ Grove (terr _) (bend a x v):= ⟨mem_union_left _ (trace_source ..), (trace_g ..).unite (trace_g ..) (trace_source ..) (trace_source ..)⟩
lemma bent_G(a:Shape)(x y:HopK n)(j:Trip m n): east a x∈ Ferry a x y j∧ east a y∈ Ferry a x y j ∧ Grove (terr _) (Ferry a x y j):=by
 let v:=east a x; let S:= Beam a x y
 have hx: v∈ S:= trace_source ..
 refine ⟨mem_union_left _ hx,mem_union_left _ ?_,?_⟩; · have ht:= trace_last v (rayW a (shiftH (terse x) (terse y))); rwa [show stop _ _ = east a y by unfold v east; rw [ray_s,stopH]] at ht -- rw modifies S?
 apply trunk (mem_union_left _ hx); intro i hi; rcases mem_union.mp hi with p|p
 · exact orig_sub (rooted (trace_g (east a x) (rayW a (shiftH ..))) v hx i p) subset_union_left
 obtain ⟨j,e,k⟩:=mem_biUnion.mp p; exact orig_sub (rooted ((bend_G ..).2) v (bend_G ..).1 i k) (fun i hi=>mem_union_right S (mem_biUnion.mpr ⟨j,e,hi⟩))
lemma pays_h(x y:HopK n)(j:Trip m n)(k:Fin m)(a:Shape): ((rayW a (boot (terse x) (j k))).length:ℝ)≤ pays x y j:=by
 rw [ray_L]; apply le_trans (b:= ((8*((dial (terse x) (j k))+1):ℕ):ℝ)) (by exact_mod_cast leanB (terse x) (j k))
 let R:=gear (x,Classical.ofNonempty) (y, Classical.ofNonempty); have he:0≤R:= Nat.cast_nonneg _; let Y:=(∑ i,(dial (terse x) (j i):ℝ)); have ht:(dial (terse x) (j k):ℝ)≤ Y:= single_le_sum (f:=fun i:Fin m=> (dial (terse x) (j i):ℝ)) (fun i _=>Nat.cast_nonneg _) (mem_univ _)
 push_cast; change _≤8*(1+(R+Y)); linarith
lemma pays_L(x y:HopK n)(j:Trip m n)(a:Shape): ((rayW a (shiftH (terse x) (terse y))).length:ℝ)≤ pays x y j:=by
 rw [ray_L]; let R:=gear (x,Classical.ofNonempty) (y, Classical.ofNonempty); have hx:0≤R:=Nat.cast_nonneg _; let Z:=(∑ i, (dial (terse x) (j i):ℝ)); have he:0≤Z:=sum_nonneg fun i _=> Nat.cast_nonneg _
 have hp:= short (terse x) (terse y); have hf:((shiftH (terse x) (terse y)).length:ℝ)≤4*R:=by change _≤4*(separation (terse x) (terse y):ℝ); exact_mod_cast hp
 change _≤8*(1+(R+Z)); linarith
lemma pays_F(a:Shape)(x y:HopK n)(j:Trip m n): (↑(Ferry a x y j).card:ℝ)≤(1+2*m)*(1+pays x y j):=by
 have hx(w:Walk)(o:Site (More n))(h:(w.length:ℝ)≤pays x y j): (↑(traceP o w).card:ℝ)≤1+pays x y j:=by apply le_trans (b:=(w.length:ℝ)+1) (by exact_mod_cast trace_k o w); linarith
 have ht (i: Fin m): (↑(bend a x (j i)).card:ℝ) ≤ 2*(1+pays x y j):=by
   let V:=rayW a (boot (terse x) (j i)); apply le_trans (b:= (↑(traceP (east a x) V).card:ℝ)+(traceP (east a x) (reverse V)).card) (by unfold bend; exact_mod_cast card_union_le _ _); rw [two_mul]; exact add_le_add (hx V _ (pays_h ..)) (hx (reverse V) _ (by simpa [Lattice.reverse] using (pays_h x y j i a : (V.length:ℝ) ≤ _)))
 unfold Ferry; let N:=univ.biUnion (fun i=> bend a x (j i)); calc
  _ ≤ (↑(Beam a x y).card:ℝ)+N.card:=by exact_mod_cast card_union_le _ _
  _ ≤ (1+pays x y j)+∑ i,2*(1+pays x y j):=add_le_add (hx _ _ (pays_L ..)) (le_trans (b:= ∑ i,(↑(bend a x (j i)).card:ℝ)) (by exact_mod_cast card_biUnion_le) (sum_le_sum fun i _=>ht i))
  _ = _:=by simp; ring
lemma grant (T:ℝ)(h:0<e)(a:Shape)(x y:HopK n)(j:Trip m n)(H:∀ t:Cin,‖spurY t‖≤T)(F: Fin m→ Cin)(p:0≤T):Had ((2*(T*titanic e (pays x y j)))^m) e (Ferry a x y j) (fun X=> ∏ k:Fin m, spurY (F k) (whirl (east a x) (rayW a (boot (terse x) (j k))) X)):=by
 let Z(k:Fin m)(X:Chin n):=(spurY (F k)) (whirl (east a x) (rayW a (boot (terse x) (j k))) X)
 let Q:=T*titanic e (pays x y j); let S:=Ferry a x y j; have hv:0≤Q:=mul_nonneg p (Real.exp_pos _).le
 have hp(k: Fin m): Had Q e S (Z k):= (((whirl_T _ _ h _ (pays_h ..)).fin (spurY (F k))).spill (mul_le_mul_of_nonneg_right (H _) (Real.exp_pos ..|>.le))).raise hv (fun i hi=>mem_union_right _ (mem_biUnion.mpr ⟨k,mem_univ _,hi⟩))
 have ht(s: Finset (Fin m)): Had ((2*Q)^s.card) e S (fun x=> ∏ k∈s,Z k x):=by
   induction s using Finset.induction_on with
   | empty=> simp only [prod_empty,card_empty,pow_zero]; exact ⟨by simp,fun A B=>by rw [sub_self,norm_zero,one_mul]; exact (forum n e).pos ..⟩
   | @insert i V he ih=> simp_rw [prod_insert he,card_insert_of_notMem he,pow_succ',mul_assoc]; exact (hp i).forge ih hv (by positivity)
 simpa only [card_univ,Fintype.card_fin] using ht univ

def netP (P:Toy m n)(x y:HopK n)(j:Trip m n)(k:Slot):=∑ l:Slot, ‖P (x,k) (y,l) j‖
def ruby(m:ℕ)(U W Z:ℝ):ℝ:=2*((↑(Fintype.card (Fin m→Cin)):ℝ)*(2*(U*Z))^m*W^m)*Z
lemma star_F(P:Toy m n)(h:0<e)(a:Shape)(x y:HopK n)(j:Trip m n)(U W:ℝ)(X:∀ t:Cin,‖sol t‖≤W)(H:∀ t:Cin,‖spurY t‖≤U)(l:0≤U)(r:0≤W)(k z:Slot): Had (ruby m U W (titanic e (pays x y j))*netP P x y j k) e (Ferry a x y j) (fun X=> spark P a x y j X k z):=by
 let Z:=titanic e (pays x y j); have hz:0≤Z:=(Real.exp_pos _).le
 let N:=(↑(Fintype.card (Fin m→Cin)):ℝ); let B:=(2*(U*Z))^m; have hB:0≤B:=by unfold B; positivity
 let O:=Ferry a x y j
 let A(v:Chin n): Op Slot:=flaw P x y j (fun k=>whirl (east a x) (rayW a (boot (terse x) (j k))) v); let G(d:Slot):=‖P (x,k) (y,d) j‖
 have hx(d:Slot): Had ((N*B*W^m)*G d) e O (fun v=> A v k d):=by
    unfold A flaw; simp_rw [Matrix.sum_apply,Matrix.smul_apply]; let V:= P (x,k) (y,d) j
    have hu (F: Fin m→ Cin): Had (B*(W^m*G d)) e O (fun X=> (∏ t, spurY (F t) (whirl (east a x) (rayW a (boot (terse x) (j t))) X)) * V (fun k=>sol (F k))) :=by
       have hp:Had B e O _:=grant U h a x y j H F l
       let z:=V (fun k=> sol (F k)); have he:‖z‖≤W^m*G d:=by apply (V.le_opNorm _).trans; rw [mul_comm _ (G d)]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); calc
         _ ≤ ∏ _i:Fin m,W:=prod_le_prod (fun k _=>norm_nonneg _) (fun k _=> X _)
         _ = _:=by simp
       refine ⟨fun v=>by rw [norm_mul]; exact mul_le_mul (hp.base _) he (norm_nonneg _) hB,fun v u=>?_⟩; rw [←sub_mul,norm_mul,mul_right_comm B]; exact mul_le_mul (hp.high ..) he (norm_nonneg _) (by apply mul_nonneg hB; exact (forum n e).pos ..)

    apply (Had.sumT _ _ _ hu).spill; exact le_of_eq (by rw [sum_const,nsmul_eq_mul]; unfold N; rw [card_univ]; ring)
 have hp(d:Slot): Had Z e O (fun X=> (track X (east a x) (rayW a (shiftH (terse x) (terse y)))).1 d z):=by
    have hu:= Had.raise (trailK (east a x) _ h _ (pays_L x y j a)) hz (show Beam a x y ⊆ O from subset_union_left)
    let L:Twig→L[ℂ]ℂ:=LinearMap.toContinuousLinearMap (show Twig→ₗ[ℂ]ℂ from { toFun:=fun x=>x.1 d z,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl })
    refine (hu.fin L).spill (mul_le_of_le_one_left hz (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=>?_))
    rw [one_mul]; exact (norm_entry x.1 d z).trans (le_max_left ..)
 simp_rw [spark,Matrix.mul_apply]; apply (Had.sumT _ _ _ (fun d=> (hx d).forge (hp d) (by unfold N G; positivity) hz)).spill; unfold ruby netP; rw [mul_sum]; exact sum_le_sum fun i _=> le_of_eq (by unfold N B G Z; ring)
end YM.CF.Moire
