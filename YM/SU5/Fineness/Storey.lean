import YM.SU5.Fineness.LeadToll
/-!
# Rough lower bill on *classical* lattice benchmark determinant, normalized by
 number of gauge-grid sites. Polynomial prefactors allowed while any n.
 Avoid IR eigenvalue estimates or mass perturbation. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
noncomputable section
namespace YM.Fineness
open Function Matrix Finset Lattice Wilson RG Exterior Precision Tree
open scoped Matrix BigOperators
variable {I J L:Type*}[Fintype I][Fintype J][DecidableEq I]{H:Sheet I}
def Tallied (M: Matrix I L ℝ):=∃ P:Matrix I L ℤ,(P.map (Int.castRingHom ℝ))=M
lemma tallied {P:Tab I J}(h:∀ i j,∃ v:ℤ,P i j= (v:ℝ)): Tallied P:=by choose f v using h; exact ⟨Matrix.of f,by ext; exact (v ..).symm⟩
namespace Tallied
lemma multi {P:Tab I J}{K:Tab J L}(p:Tallied P)(q:Tallied K): Tallied (P*K):=by obtain ⟨a,rfl⟩:=p; obtain ⟨b,rfl⟩:=q; exact ⟨a*b,Matrix.map_mul ..⟩ -- map_mul binder?
lemma plus_t {A B:Tab I L}(p:Tallied A)(q:Tallied B): Tallied (A+B):=by obtain ⟨a,rfl⟩:=p; obtain ⟨b,rfl⟩:=q; exact ⟨a+b,Matrix.map_add (Int.castRingHom ℝ) (fun a b=> map_add (Int.castRingHom ℝ) a b) a b⟩
lemma twisted {A:Tab I L}(p:Tallied A):Tallied Aᵀ:=by obtain ⟨a,rfl⟩:=p; exact ⟨aᵀ,rfl⟩
lemma duo {A:Tab I J}{B:Tab I L}(p:Tallied A)(q:Tallied B): Tallied (fromCols A B):=by obtain ⟨a,rfl⟩:=p; obtain ⟨b,rfl⟩:=q; exact ⟨_,fromCols_map a b _⟩
lemma at_least (p:Tallied H)(h:0<H.det): 1 ≤ H.det:=by
 obtain ⟨a,rfl⟩:=p; have hf:(a.map (Int.castRingHom ℝ)).det= (a.det:ℝ):=(Int.cast_det a).symm
 rw [hf] at h ⊢; have ht : 0 < a.det:= by exact_mod_cast h
 exact_mod_cast (show 1 ≤ a.det from by omega)
end Tallied
variable {n:Side}{s u:ℝ}{T:Sheet (Body 2 n)}
local notation "D"=>d 1 n
local notation "X"=> sightZero n
local notation "V₀" => Fintype.card (Site n)
lemma bond_count (n:Side) : Fintype.card (Body 1 n)=4* Fintype.card (Site n):= by rw [show Fintype.card (Body 1 n)=_ from Fintype.card_prod .., Fintype.card_congr (axisEquiv.symm)]; simp [Axis,Nat.mul_comm]
private lemma curl_int(n:Side): Tallied (d 1 n):=by
 refine tallied fun ⟨x,i⟩ z=> ?_; obtain ⟨u,rfl⟩:=plaqEquiv.surjective i
 obtain ⟨⟨i,b⟩,q⟩:=u; have he:= d_plaquettes x ⟨(i,b),q⟩ (Pi.single z 1); simp only [mulVec,dotProduct_single,mul_one] at he
 rw [plaq_map,he]; let f(a:Body 1 n):ℤ:= if z=a then 1 else 0; have h(a): (Pi.single z (1:ℝ): Body 1 n → ℝ) a=(f a:ℝ):=by unfold f; split; rename_i r; simp [r]; rename_i t; simp [Pi.single_eq_of_ne (Ne.symm t)]
 simp_rw [h]; rw [←Int.cast_sub, ←Int.cast_sub, ←Int.cast_sub]; exact ⟨_,rfl⟩
lemma flags_root (p:Puncture n)(x:Site n): (switch n) (x,vac) p=if x=p.val then 1 else 0:=by simp [switch,FreeResolvent.insertion,eq_comm]
lemma blade (p:Puncture n)(x:Site n)(i:Axis) : rootGrad n (x,coord i) p=(if x=p.val - step i then 1 else 0) -(if x=p.val then 1 else 0):=by
 let Φ:=fun i:Body 0 n=> (switch n) i p
 rw [show rootGrad n (x,coord i) p=(d 0 n *ᵥ Φ) (x,coord i) from rfl, d_sites]; simp only [Φ,flags_root,eq_sub_iff_add_eq]
private lemma index_int(n:Side): Tallied (sightZero n):=by
 refine Tallied.duo ?_ ?_ -- fromCols
 · refine tallied fun ⟨x,i⟩ z=>?_ ; obtain ⟨b,rfl⟩:=axisEquiv.surjective i; rw [coord_map,blade]; split_ifs  <;> (first| (refine ⟨0,?_⟩; solve|norm_num) | (refine ⟨1,?_⟩; solve|norm_num) | (refine ⟨-1,?_⟩; solve|norm_num))
 refine tallied fun i k=>?_ ; unfold harmonic; rw [of_apply]; split <;> first| exact ⟨0,(Int.cast_zero).symm⟩ | exact ⟨1,(Int.cast_one).symm⟩
lemma honorX (h:T.PosDef): (Precision.K T + X*Xᵀ).PosDef:=by
 let A:= K T; have hx:= lattice_null _ ((q_iff _).1 h).1
 apply (q_iff _).2; refine ⟨?_,fun x u=>?_⟩
 · rw [transpose_add,hx.symmA]; simp
 rw [priced_plus,show qpay (K T) x=qpay T (D*ᵥ x) from qgain T x,show qpay (X*Xᵀ) x=_ from (show qpay ((X)* _) x=dotProduct (Xᵀ *ᵥ x) (Xᵀ *ᵥ x) from gram_price (T:=Xᵀ) x)]
 by_cases g: D*ᵥ x=0
 · apply add_pos_of_nonneg_of_pos (cost_zero T h _); apply l2pos; intro he; refine u (no_wind g (fun t=> ?_))
   rw [← dotProduct_transpose_mulVec,he,dotProduct_zero]
 exact add_pos_of_pos_of_nonneg (q_at T h g) (FreeResolvent.normSum_nn _)
lemma limited_grain (n:Side) : ((sightZero n)ᵀ*sightZero n).trace ≤ 100 * (Fintype.card (Site n):ℝ):=by
 let E:= rootGrad n; let H:= harmonic n
 let N:ℝ:= Fintype.card (Site n); let I:= Body 1 n
 have ht(p:Puncture n)(a:Axis) : ∑ x:Site n,E (x,coord a) p*E (x,coord a) p ≤2:=by
    let f(x:Site n):ℝ:=if x=p.val-step a then 1 else 0; let g(x:Site n):ℝ:=if x=p.val then 1 else 0
    refine (sum_le_sum (g:=fun i=> f i+g i) (fun i _=> ?_)).trans ?_
    · unfold E; rw [blade]; unfold f g; split_ifs <;> norm_num
    rw [sum_add_distrib]; simp [f,g]; norm_num
 have he(p) : ∑ i:I,E i p*E i p ≤ 8:=by
    rw [Fintype.sum_prod_type,sum_comm]; rw [←axisEquiv.sum_comp]; exact (sum_le_sum (g:=fun _=>(2:ℝ)) (fun i _=>ht p i)).trans (by norm_num [Axis])
 have hg (p): ∑ i:I,H i p*H i p≤ 4*(Fintype.card (Site n):ℝ):=by
    refine (sum_le_sum (g:=fun _=> (1:ℝ)) (fun i _=>?_)).trans_eq ?_; unfold H harmonic; rw [of_apply]; split_ifs <;> norm_num
    simp only [sum_const,card_univ,nsmul_eq_mul,mul_one]; rw [show Fintype.card I=_ from bond_count n,Nat.cast_mul,Nat.cast_ofNat]
 unfold Matrix.trace; rw [Fintype.sum_sum_type]; simp only [diag_apply,mul_apply,transpose_apply,sightZero,fromCols_apply_inl,fromCols_apply_inr] -- names
 refine (add_le_add (sum_le_sum (fun i _=>he i)) (sum_le_sum (fun i _=>hg i))).trans ?_
 have hp: (Fintype.card (Puncture n):ℝ) ≤ Fintype.card (Site n):=by exact_mod_cast Fintype.card_subtype_le _
 simp only [sum_const,nsmul_eq_mul,card_univ]; rw [show Fintype.card Axis=4 by simp [Axis],Nat.cast_ofNat]; nlinarith only [hp, (by positivity: 0 <(Fintype.card (Site n):ℝ))]
local notation "T_"=>s • (1:Sheet (Body 2 n))
lemma tariff (hu:0<s)(u:s ≤1)(h:FreeResolvent.Gap T s)(he:Tᵀ=T): (4*Real.log s-200)*(Fintype.card (Site n):ℝ)≤ Real.log (leasePart T):=by
 let t:=qpos hu he h; let Z:= X * Xᵀ; let W:Sheet (Body 1 n):= Dᵀ * D+Z; let A := K T+Z; let V:= Precision.K (1: Sheet (Body 2 n))+Z; have hp : W=V:= by unfold W V Precision.K; rw [Matrix.mul_one]
 have hz:A.PosDef:= honorX t; have ht: W.PosDef:=hp.symm ▸ (show V.PosDef from honorX Matrix.PosDef.one)
 have hf: Tallied W:= ( (curl_int n).twisted.multi (curl_int n) ).plus_t ( (index_int n).multi (index_int n).twisted)
 have hχ:=ht.det_pos; have hb:1≤W.det:= hf.at_least hχ
 have hc :(s • W).det ≤ A.det:= by
    refine (harvested (pen_left s hu ht) ((q_iff _).1 hz).1 (fun x=>?_)).2; rw [hp,rates,priced_plus,priced_plus]; rw [mul_add]; apply add_le_add
    · unfold K; rw [qgain 1,qgain T]; exact (by simpa only [qpay, Matrix.one_mulVec] using (h.lower (D*ᵥ x)))
    apply mul_le_of_le_one_left _ u; rw [show qpay Z x= _ from gram_price (T:=Xᵀ) x]; apply FreeResolvent.normSum_nn
 have he:= volume_ceiling (lattice_null T he).rail.gramPos; have heX: 0<((X)ᵀ * X).det:= (lattice_null T ((q_iff _).1 t).1).rail.gramPos.det_pos
 have hW: A.det=leasePart T*((Xᵀ*X).det)^2:= open_volume (lattice_null T ((q_iff _).1 t).1)
 rw [det_smul,bond_count] at hc
 have hz := Real.log_le_log (show 0<s^(4*V₀) from pow_pos hu _) ((le_mul_of_one_le_right (by positivity) hb).trans hc)
 rw [hW,Real.log_mul (lattice_pos t).ne' (pow_ne_zero _ heX.ne'),Real.log_pow, Real.log_pow] at hz; push_cast at hz
 have hh:= limited_grain n; linarith
end YM.Fineness
#print axioms YM.Fineness.tariff
