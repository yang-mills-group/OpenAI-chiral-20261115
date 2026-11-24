import YM.SU5.FiniteGaugeData.Pannier.Fragile
import YM.SU5.FiniteGaugeData.Pannier.Majus
/-! # Absolute price expanding the observing-level ket by numbers of arbitrary
unit-op-norm single CAR letters, under the real Mark. Consume real p.*, not narrow-span state. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Pannier.Damask
open Filter Function NormedSpace Lattice Wilson Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Branch Dial Nacre Font Laic Graph Skye
open scoped Pointwise Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
open Py.Rate.Pannier
variable {N:Side}{v t u e C a:ℝ} {A0:Loom N} {r d:ℕ}
def RayPrice (A:Pane N) (i:Seat N) (v a:ℝ) := ∀ j:Pec.Ok N, ‖silt i j A‖ ≤ v * Real.exp (a*Font.dial i j)
open RG
-- explicit ramp. outside a dirty halo.
private lemma leafRow (U:Pane N)(x:Seat N)(t: x∉ Lattice.halo r (flags v U))(e:r ≤ (More N).val) (w:v≥0)(s:0≤a) : RayPrice U x (v+2*Real.exp (-(a*r))) a:=by
 intro j
 let A:= (v+2*Real.exp (-(a*r)))
 have he(j:Pec.Ok N)(h:r ≤ Font.dial x j) : ‖silt x j U‖ ≤ A*Real.exp (a*Font.dial x j):=by
    apply (group.curvature_norm _).trans; apply (group.chord_le_two _) |>.trans; unfold A; rw [add_mul]; refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg w (Real.exp_pos _).le)); rw [mul_assoc, ←Real.exp_add]; apply le_mul_of_one_le_right (by norm_num); apply Real.one_le_exp; linarith [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr h) s]
 cases j with
 | inl i=>
    by_cases f:r < Font.dial x (Sum.inl i); · exact he _ f.le
    have hy: i.1∉ flags v U:= by intro W; apply t; apply halo_spec.mpr; exact ⟨i.1,W,(separation_comm ..).trans_le (le_of_not_gt f)⟩
    let y:=i.1; let p:Face (Per (More N)):= i; have hh: group.chord (faceValue U p) ≤ v:=by
       by_contra! t; exact hy ((flags_spec ..).mpr ⟨i,Work.E01.base_touched _,t⟩)
    apply (group.curvature_norm _).trans; let T:=shiftH x y; have ht:stop x T=y:=stopH ..; rw [Nacre.boot, travel_append,travel_append,stop_append]; simp_rw [show stop x (shiftH x i.1)=i.1 from ht,square_stop]; rw [show travel U i.1 _= _ from (show travel U y (reverse T)=(travel U x T)⁻¹ from (by nth_rw 1 [←ht]; rw [travel_reverse]))]; rw [group.chord_conj]
    exact hh.trans (le_trans (le_add_of_nonneg_right (by positivity)) (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))))
 | inr i=> exact he _ e
variable {m:ℕ}
lemma cavil_row_reduced (T:Toy m N)(p:CardK N m T C a)(A:Pane N)(e:0≤a)(w:0≤v)(s:Signed)(i:Single N) (t: RayPrice (Yg (Nacre.incX s) A) (place_x i) v a) :
    ∑ j:Single N, ‖cavil T (Yg (Nacre.incX s) A) i j‖ ≤ 45*(v^m*C):=by
  let V:=Yg (Nacre.incX s) A; let f(k: Trip m N) (x: Fin m):= silt (terse i.1) (k x) V
  have ht(k j):∏ x:Fin m,‖f k x‖ ≤ v^m*nick a (notx m i j k):=by
    let W(x):=t (k (x: Fin m)); refine (prod_le_prod (fun x _=>norm_nonneg (f k x)) (fun x _=>W x)).trans ?_
    rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,←Real.exp_sum,←mul_sum]; refine mul_le_mul_of_nonneg_left (le_trans (b:=Real.exp (a*notx m i j k)) ?_ ?_) (pow_nonneg w _)
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (show 0≤gear _ _ by unfold gear; positivity)) e)
    exact le_mul_of_one_le_left (Real.exp_pos _).le (le_add_of_nonneg_right (notx_zero ..))
  let F(k:Trip m N)(j:Single N):=nick a (notx m i j k)*‖T i j k‖
  let G(q:HopK N)(z:SU.Slot)(k:Trip m N):=F k (q,z)
  have hp(k: Trip m N)(j:Single N): ‖mold T i.1 j.1 k V i.2 j.2‖ ≤ ∑ q:SU.Slot, (v^m* F k (j.1,q)) := by -- tune j binder
    unfold mold; rw [Matrix.mul_apply]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro q _; rw [norm_mul]; have hx: ‖walkB i.1 j.1 V q j.2‖ ≤ 1:= (norm_entry (walkB _ _ V) _ _).trans (le_of_eq (CStarRing.norm_of_mem_unitary (matter _).property)); apply (mul_le_of_le_one_right (norm_nonneg _) hx).trans; change ‖T i _ k (f k)‖ ≤ v^m * F k _; refine ((T i (j.1,q) k).le_opNorm (f k)).trans ((mul_le_mul_of_nonneg_left (ht k (j.1,q)) (norm_nonneg _)).trans_eq ?_); unfold F; ring
  have he (x): ‖cavil T V i x‖ ≤ v^m*(∑ q:SU.Slot,∑ k,G x.1 q k):=by
    unfold cavil; rw [Matrix.of_apply,Matrix.sum_apply]; apply (norm_sum_le ..).trans; rw [mul_sum]; simp_rw [mul_sum]; rw [sum_comm (f:=fun q k=> v^m*G _ q k)]; exact sum_le_sum fun k _=> hp k x
  let V'(k : HopK N):=v^m*(∑ q:SU.Slot,∑ i,G k q i)
  apply (sum_le_sum (g:=fun q:Single N=>V' q.1) (fun q _=>he q)).trans
  have ht: balance a T i= ∑ q:HopK N,∑ k:SU.Slot,∑ i,G q k i :=by rw [balance,Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]; simp only [sum_const,card_univ,SU.slots,nsmul_eq_mul,Nat.cast_ofNat]
  rw [←mul_sum]; apply mul_le_mul_of_nonneg_left _ (by positivity); unfold V'; rw [←mul_sum,←ht]; exact mul_le_mul_of_nonneg_left (p.2.2 i) (pow_nonneg w _)
private def Hawk (S:Finset (Seat N)):Finset (Single N):= univ.filter (fun i=> place_x i ∈ S)
open Tenant
lemma hawk_budget (S:Finset (Seat N)):(Hawk S).card ≤ S.card*180:=by
 let f(i:Single N) := (place_x i, i.1.2,i.2)
 let X:= S ×ˢ (univ: Finset (SpinIdx × SU.Slot))
 have hx(j : Single N)(p:j∈ Hawk S): f j∈ X:= mem_product.mpr ⟨(mem_filter.mp p).2,mem_univ _⟩
 rw [← card_image_of_injective (Hawk S) (show Injective f from fun ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩ e=> by obtain ⟨v,h,w⟩ : x=y ∧ i=k ∧ j=l:= ⟨needle (congrArg Prod.fst e),congrArg (fun i=> i.2.1) e, congrArg (fun i=> i.2.2) e⟩; rw [v,h,w])]
 apply (card_le_card (image_subset_iff.mpr hx)).trans_eq ?_; unfold X; rw [card_product,card_univ,Fintype.card_prod,SU.slots, show Fintype.card SpinIdx=4 from Fintype.card_fin _]
abbrev quake (r d:ℕ)(C:ℝ):=4*C* (((r+4)*2+1:ℕ)^4:ℕ)*((d+d+1:ℕ)^4:ℕ)*180
-- C count of faces; uses absolute volumes
abbrev storm (X:Orbit N)(v e:ℝ)(r d:ℕ)(C:ℝ)(m:ℕ):ℝ:=(Fintype.card (Single N):ℝ)*(45*(e^m*C)) + quake r d (flakes v X.1) * (45*((2:ℝ)^m*C))
open Fixed.Extensive
private lemma bolt_saw (U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(T:Toy m N)(p:CardK N m T C a)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e)(i:Signed) :
    absEntries (cavil T (Yg (incX i) (A0 U))) ≤ storm U v e r d C m:=by
 let A:= Yg (incX i) (A0 U); let B:= (Lattice.halo d (flags v A)); let H:= Hawk B; let D:=45*((2:ℝ)^m*C); let E:=45*(e^m*C); let y:=quake r d (flakes v U.1); let f(j:Single N) := ∑ k:Single N, ‖cavil T A j k‖
 have hp : 0≤ v+2*Real.exp (-(a*d)):=by positivity
 have ht:0≤E:=by unfold E; have he:=hp.trans q; positivity
 have he:(∑ j,f j) ≤ ∑ j:Single N,(E+if j∈ H then D else 0):=by
    apply sum_le_sum; intro j _; split
    · exact (Fixed.Extensive.cavilRow T p (A0 U) (railT _ _ s) s (by positivity) i j).trans (le_add_of_nonneg_left ht)
    rename_i V; rw [add_zero]; apply le_trans (cavil_row_reduced T p (A0 U) s hp i j (leafRow A (place_x j) (fun k=>V (mem_filter.mpr ⟨mem_univ _,k⟩)) l w s)); unfold E; gcongr
 have hv:B=(Lattice.halo d (flags v (pull i 0 (A0 U)))):=by unfold B A; rw [Ywin i]
 apply he.trans; rw [sum_add_distrib,sum_ite,sum_const,sum_const,sum_const_zero]; simp_rw [card_univ,nsmul_eq_mul,add_zero]; rw [filter_mem_eq_inter,univ_inter]; unfold storm; gcongr
 have hk:= grease_f g U ℓ d i; rw [←hv] at hk
 have hz:= (hawk_budget B).trans (Nat.mul_le_mul_right 180 hk); have he:(H.card:ℝ)≤ y:= by unfold H y quake flakes; exact (Nat.cast_le.mpr hz).trans (Eq.le (by push_cast; ring))
 exact he
private lemma pays_foil_sum (F:Signed→ FC (Single N)) (C:ℝ) {v:ℝ}(H:∀ s,Pays v (F s) C): Pays v ((Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed,F s) C:=by
 let Q:=Fintype.card Signed; have ht:= (Pays.sumT univ F (fun _=> C) (fun x _=>H x)).linear ((Q:ℝ)⁻¹:ℝ)
 have he : 0<(Q:ℝ):=by unfold Q; exact_mod_cast Fintype.card_pos
 rw [Complex.norm_real,Real.norm_of_nonneg (by positivity),sum_const,card_univ,nsmul_eq_mul, inv_mul_cancel_left₀ he.ne'] at ht -- syntactic Q issue
 exact ht
private lemma tender_dT {h:ℝ}(hH:0≤h)(U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(T:Toy m N)(p:CardK N m T C a)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e) (P:Op (Single N))(Hp:IsStarProjection P) : Pays h (dg (Kennel.capT P (colorX T (A0 U)))) (storm U v e r d C m*h^2):=by
  let Q:=1-P; let K : Op (Single N) →ₗ[ℝ] FC (Single N):=
    { toFun F:=dg (Q*F*P)
      map_add' i j:=by rw [mul_add,add_mul,dg_add]
      map_smul' c F:=by rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,dg_scale]; rfl }
  let D(s):= Nacre.foil s (cavil T) (A0 U)
  change Pays h (K (_ • ∑ s:Signed,D s)) _
  rw [map_smul,map_sum]; apply pays_foil_sum; intro i; let L:= cavil T (Yg (incX i⁻¹) (A0 U))
  change Pays h (dg (Q* Nacre.foil i (cavil T) (A0 U)*P)) _ ; rw [Nacre.foil,Nacre.zone_c]
  exact (Pays.jazzG hH _ _ L Q P (Hp.one_sub.norm_le _) (Hp.norm_le _)).weigh (mul_le_mul_of_nonneg_right (bolt_saw U g ℓ s w l T p c e q i⁻¹) (sq_nonneg _)) hH
private lemma dgActC {h β γ D:ℝ}{j:ℕ}(R:GramM N)(L:Ledger D β γ a C R)(hH:0≤h)(U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e)(p:IsStarProjection (spar j R.J.M (A0 U))) : Pays h (dg (actF j R A0 U)) ((storm U v e r d C 1+storm U v e r d C 2)*h^2):=by
 unfold actF Aim.den; rw [Pi.add_apply]; obtain ⟨A,B⟩:= L.field.1
 rw [show ∀ (x y z:Op (Single N)),Kennel.capT x (y+z)=Kennel.capT x y+Kennel.capT x z from fun _ _ _=>by unfold Kennel.capT; rw [mul_add,add_mul],dg_add,add_mul]
 exact (tender_dT hH U g ℓ s w l _ A c e q _ p).add (tender_dT hH U g ℓ s w l _ B c e q _ p)
private lemma mile_duly {D u₁ u₂ h:ℝ}{j:ℕ}(R:GramM N)(L:Ledger D u₁ u₂ a C R)(hH:0≤h)(hw:h≤D)(U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e)(p:IsStarProjection (spar j R.J.M (A0 U))) : Pays h (mile j R A0 U) (Real.exp (pittance N 2 C+((u₁+u₁+u₂)*(More N).val^4+ (storm U v e r d C 1+storm U v e r d C 2)*h^2))) :=by
 have h₀:= dgActC R L hH U g ℓ s w l c e q p
 have he:= Pays.boardH N R U u₁ u₂ C a D L _ p hH hw
 let Q:=Pec.pigment R.J.I (A0 U); let E:= pittance N 2 C; have hf:‖-Q‖ ≤ E:= by rw [norm_neg]; exact aurP _ _ L.field.2 (railT _ _ s) (by positivity)
 apply ((((he.mul (h₀.expo)).linear (Complex.exp (-Q)))).weigh ?_ hH)
 rw [Real.exp_add, Real.exp_add ((u₁+u₁+u₂)*_)]
 exact mul_le_mul_of_nonneg_right ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp_of_le hf)) (by positivity)

-- pricing threshold once h chosen high. Constant of the coefficient of #sites C pre-B,
-- K per bad face later; declare ANY fixed h', then high-x may depend on it. Record ledger names.
open CF.Py.Rate
private lemma pang {d r:ℕ}{C h:ℝ}(c:0≤C) (p:0≤h)(e:ℝ)(U:Orbit N)(v:ℝ) : (storm U v e r d C 1+storm U v e r d C 2)*h^2 ≤ (180*45*C*h^2*(e+e^2))*(((N.val:ℕ):ℝ)^4) + (quake r d 1*(45*6*C)*h^2)*flakes v U.1 := by
 apply le_of_eq; unfold storm quake; rw [Pic.units_t (N:=N)]; ring
private lemma bedtime (a X:ℝ)(s:0<a)(l:0<X) : ∃ d:ℕ,2*Real.exp (-(a*d)) ≤ X:=by
 apply Filter.Eventually.exists (f:=atTop); have ht:Tendsto (fun i:ℕ=> 2*Real.exp (-(a*i))) atTop (𝓝 0):=by
    simpa only [mul_zero,Function.comp_apply] using (((Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop s))).const_mul 2))
 exact ht.eventually (ge_mem_nhds l)
-- consumers from any Bought Ledger. eventually t thresholds, age high of actual price. tolerance→epochs. D may be h.
open Pressure
abbrev cameo (C:ℝ) := 3*3+4*C
lemma wisps_budget {h a C u t:ℝ}{r:ℕ}(p:0≤h)(c:0≤C)(uP:0<u)(s:0<a): ∃ κ : ℝ,0≤κ ∧ ∀ᶠ x:ℝ in atTop,∃ n:ℕ,∀ {N:Side}{R:GramM N}{A0:Loom N}(p₁:Roof N u t r A0) (D u₁ u₂:ℝ)(j:ℕ)(l:Ledger D u₁ u₂ a C R), h≤ D → n≤ N.val → u₁ ≤ 1 → u₂ ≤ 1 → ∀ z:Orbit N, IsStarProjection (spar j R.J.M (A0 z)) → Pays h (mile j R A0 z) (Real.exp ((cameo C)*sites N + κ*flakes (temp x) z.1)):=by
 let f(y:ℝ):=180*45*C*h^2*(y+y^2); have he:Continuous f:=by unfold f; fun_prop
 have hh:f 0 <1:= by simp [f]
 have hf: ∀ᶠ i:ℝ in nhdsWithin 0 (Set.Ioi 0),f i< 1 := eventually_nhdsWithin_of_eventually_nhds (he.continuousAt.tendsto.eventually (gt_mem_nhds hh)); obtain ⟨e,he',t'⟩:= (hf.and self_mem_nhdsWithin).exists; change 0 < e at t'
 obtain ⟨d,l⟩:=bedtime a (e/2) s (half_pos t')
 let k:=quake r d 1*(45*6*C)*h^2; refine ⟨k,by unfold k quake; positivity,?_⟩; have ht:Tendsto temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
 filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually (ge_mem_nhds (half_pos t')),ht.eventually (ge_mem_nhds uP)] with x hx v w; let y:= temp x; refine ⟨d,fun {N R A0} a' D u₁ u₂ j H hv hd h1 h2 Z X =>?_⟩
 have h0:y≥0:= (Work.E09.temp_pos hx).le
 have hl := mile_duly (u:=u) R H p hv Z a' w s.le h0 (hd.trans (Nat.le_mul_of_pos_right _ two_pos)) c e (show y+2*Real.exp (-(a*(d:ℝ)))≤e from (by change y≤e/2 at v; linarith only [v,l])) X
 refine hl.weigh (Real.exp_monotone ?_) p
 apply (add_le_add_right (add_le_add_right (pang (d:=d) (r:=r) c p e Z y) _) _).trans -- `(left?)
 have H' : ((N.val:ℝ)^4) ≤ sites N:= pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.le_mul_of_pos_right N.val (by decide : (0:ℕ)<2))) _
 let V:= sites N; have hp:0≤V:=zero_le_one.trans (sites_pos _)
 change pittance N 2 C + ((u₁+u₁+u₂)*V+(f e* _ +k*flakes y Z.1)) ≤ cameo C*V + k*flakes y Z.1
 unfold pittance cameo
 linarith only [mul_le_mul_of_nonneg_right h1 hp,mul_le_mul_of_nonneg_right h2 hp,mul_le_mul_of_nonneg_left (show _ ≤ V from H') c,(show (N.val:ℝ)^4 ≤ V from H'),hp,mul_le_mul_of_nonneg_right he'.le (show 0≤(N.val:ℝ)^4 by positivity)]
end YM.CF.Pannier.Damask
#print axioms YM.CF.Pannier.Damask.wisps_budget
