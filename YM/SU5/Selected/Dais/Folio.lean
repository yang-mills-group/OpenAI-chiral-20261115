import YM.SU5.FiniteGaugeData.Pannier.Exacts
/-! Sharp variant. Reproduces needed private lemmas from FiniteGaugeData/Pannier/Exacts.lean to export strengthened arbitrary h/epsilon trade. No reproving history facts here. -/
set_option synthInstance.maxSize 8000
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Pannier.Damask.Capri
open Filter Function NormedSpace Lattice Wilson Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Branch Dial Nacre Font Laic Graph Skye
open scoped Pointwise Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
open Py.Rate.Pannier
variable {N:Side}{v t u e C a:ℝ} {A0:Loom N} {r d:ℕ}
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
private def Hawk (S:Finset (Seat N)):Finset (Single N):= univ.filter (fun i=> place_x i ∈ S)
open Tenant
lemma hawk_budget (S:Finset (Seat N)):(Hawk S).card ≤ S.card*180:=by
 let f(i:Single N) := (place_x i, i.1.2,i.2)
 let X:= S ×ˢ (univ: Finset (SpinIdx × SU.Slot))
 have hx(j : Single N)(p:j∈ Hawk S): f j∈ X:= mem_product.mpr ⟨(mem_filter.mp p).2,mem_univ _⟩
 rw [← card_image_of_injective (Hawk S) (show Injective f from fun ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩ e=> by obtain ⟨v,h,w⟩ : x=y ∧ i=k ∧ j=l:= ⟨needle (congrArg Prod.fst e),congrArg (fun i=> i.2.1) e, congrArg (fun i=> i.2.2) e⟩; rw [v,h,w])]
 apply (card_le_card (image_subset_iff.mpr hx)).trans_eq ?_; unfold X; rw [card_product,card_univ,Fintype.card_prod,SU.slots, show Fintype.card SpinIdx=4 from Fintype.card_fin _]
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
open CF.Py.Rate
private lemma pang {d r:ℕ}{C h:ℝ}(c:0≤C) (p:0≤h)(e:ℝ)(U:Orbit N)(v:ℝ) : (storm U v e r d C 1+storm U v e r d C 2)*h^2 ≤ (180*45*C*h^2*(e+e^2))*(((N.val:ℕ):ℝ)^4) + (quake r d 1*(45*6*C)*h^2)*flakes v U.1 := by
 apply le_of_eq; unfold storm quake; rw [Pic.units_t (N:=N)]; ring
private lemma bedtime (a X:ℝ)(s:0<a)(l:0<X) : ∃ d:ℕ,2*Real.exp (-(a*d)) ≤ X:=by
 apply Filter.Eventually.exists (f:=atTop); have ht:Tendsto (fun i:ℕ=> 2*Real.exp (-(a*i))) atTop (𝓝 0):=by
    simpa only [mul_zero,Function.comp_apply] using (((Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop s))).const_mul 2))
 exact ht.eventually (ge_mem_nhds l)
-- consumers from any Bought Ledger. eventually t thresholds, age high of actual price. tolerance→epochs. D may be h.
open Pressure
open CF.Pec
lemma pigments_one (T:Pride N)(x:Site N)(A:Pane N)(p:Lac T a C)(g:RayPrice A (node x) v a)(e:0≤v) : ‖Pec.tag (node x) (T x) A‖ ≤ v^2*C:=by
 let o:= node x; have ht(i j: Ok N) : ‖inner ℝ (silt o i A) (silt o j A)‖ ≤ v^2*nick a (contour o i j):=by
   apply (norm_inner_le_norm ..).trans; apply (mul_le_mul (g i) (g j) (norm_nonneg _) (mul_nonneg e (Real.exp_pos _).le)).trans; rw [mul_mul_mul_comm,←Real.exp_add,←mul_add,←sq]; refine mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le (by linarith [ct_pos o i j])) (by positivity)
 apply (norm_sum_le ..).trans; apply (mul_le_mul_of_nonneg_left (p.pay x) (sq_nonneg v)).trans'; simp_rw [Pec.cents,mul_sum]; refine sum_le_sum fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=>?_); rw [norm_smul,←mul_assoc]; exact mul_le_mul_of_nonneg_right (ht i j) (norm_nonneg _)
abbrev pit (r d:ℕ)(C:ℝ):= quake r d 1*(4*C)
private lemma pig_price(U:Orbit N)(g:Roof N u t r A0)(ℓ:v≤u)(s:0≤a)(w:0≤v)(l:d≤(More N).val)(T:Pride N)(p:Lac T a C)(c:0≤C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e) : ‖Pec.pigment T (A0 U)‖ ≤ pittance N e C + pit r d C * flakes v U.1:=by
 apply sealV; intro i; let V:=Yg (incX i) (A0 U); let B:= Lattice.halo d (flags v V); let H:=(univ:Finset (Site N)).filter fun x=>node x∈ B; have hp:0 ≤ v+2*Real.exp (-(a*d)):=by positivity
 have hv:B=(Lattice.halo d (flags v (pull i 0 (A0 U)))):=by unfold B V; rw [Ywin i]; -- counts same residue
 let D(x:Site N):=Pec.tag (node x) (T x) V; have he:∑ x, ‖D x‖ ≤ ∑ x:Site N, ((e^2*C)+ if x∈H then 4*C else 0) :=by
    apply sum_le_sum; intro j _; split
    next x=> apply (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) c)).trans'; exact (pigments_one T j V p (fun j0=> (railT _ _ s |>.fee i (node j) j0)) (by norm_num: (0:ℝ) ≤ 2)).trans_eq (by ring)
    next u=> rw [add_zero]; exact (pigments_one T j V p (leafRow V (node j) (fun v=>u (mem_filter.mpr ⟨mem_univ _,v⟩)) l w s) hp).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp q _) c)
 have hg: H.card ≤ B.card:=by
    rw [← card_image_of_injective _ needle]; apply card_le_card; exact image_subset_iff.mpr fun i x=> (mem_filter.mp x).2
 have hk:= grease_f g U ℓ d i; rw [← hv] at hk
 let F:=flakes v U.1; have ht:(H.card:ℝ) ≤ quake r d 1*F:=by
    have hx : H.card ≤ (((roughness v U.1).card*4*((r+4)*2+1)^4)*(d+d+1)^4)*180:= (hg.trans hk).trans (Nat.le_mul_of_pos_right _ (by norm_num)); apply (Nat.cast_le.mpr hx).trans_eq; unfold quake F flakes; push_cast; ring
 rw [sum_add_distrib,sum_ite,sum_const,sum_const,sum_const_zero,add_zero,filter_mem_eq_inter,univ_inter] at he; simp_rw [card_univ,site_card,nsmul_eq_mul] at he -- multiple rw
 have h : ‖zinger T V‖≤pittance N e C+pit r d C *F:=by
    apply (norm_sum_le ..).trans; apply he.trans; unfold pittance pit; push_cast; linarith only [mul_le_mul_of_nonneg_right ht (show 0≤ 4*C by positivity)]
 rw [complX]; unfold cSignX; split; rw [norm_star]; exact h; exact h
private lemma mile_duly {D u₁ u₂ h:ℝ}{j:ℕ}(R:GramM N)(L:Ledger D u₁ u₂ a C R)(hH:0≤h)(hw:h≤D)(U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e)(p:IsStarProjection (spar j R.J.M (A0 U))) : Pays h (mile j R A0 U) (Real.exp (pittance N e C+pit r d C *flakes v U.1+((u₁+u₁+u₂)*(More N).val^4+ (storm U v e r d C 1+storm U v e r d C 2)*h^2))) :=by
 have h₀:= dgActC R L hH U g ℓ s w l c e q p
 have he:= Pays.boardH N R U u₁ u₂ C a D L _ p hH hw
 let Q:=Pec.pigment R.J.I (A0 U); let E:= pittance N e C+pit r d C *flakes v U.1; have hf:‖-Q‖ ≤ E:= by rw [norm_neg]; exact pig_price U g ℓ s w l _ L.field.2 c e q
 apply ((((he.mul (h₀.expo)).linear (Complex.exp (-Q)))).weigh ?_ hH)
 rw [Real.exp_add E, Real.exp_add ((u₁+u₁+u₂)*_)]
 exact mul_le_mul_of_nonneg_right ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp_of_le hf)) (by positivity)

lemma penalize {h a C u t:ℝ}{r:ℕ}(p:0≤h)(c:0≤C)(uP:0<u)(s:0<a)(ε:ℝ)(e':0<ε) : ∃ κ γ: ℝ,0≤κ ∧ 0<γ∧ ∃ N0:ℕ,∀ᶠ x:ℝ in atTop,∀ {N:Side}{R:GramM N}{A0:Loom N}(p₁:Roof N u t r A0) (D u₁ u₂:ℝ)(j:ℕ)(l:Ledger D u₁ u₂ a C R), h≤ D → N0≤ N.val → u₁ ≤ γ → u₂ ≤ γ → ∀ z:Orbit N, IsStarProjection (spar j R.J.M (A0 z)) → Pays h (mile j R A0 z) (Real.exp (ε*sites N + κ*flakes (temp x) z.1)):=by
 let f(y:ℝ):=180*45*C*h^2*(y+y^2); let g(y:ℝ):= f y + y^2 * C+3*y; have he:Continuous g:=by unfold g f; fun_prop
 have hh:g 0 <ε:=by simpa [g,f] using e'
 have hf: ∀ᶠ i:ℝ in nhdsWithin 0 (Set.Ioi 0),g i< ε := eventually_nhdsWithin_of_eventually_nhds (he.continuousAt.tendsto.eventually (gt_mem_nhds hh)); obtain ⟨e,he',t'⟩:= (hf.and self_mem_nhdsWithin).exists; change 0 < e at t'
 obtain ⟨d,l⟩:=bedtime a (e/2) s (half_pos t')
 let k:=quake r d 1*(45*6*C)*h^2+ pit r d C; refine ⟨k,e,by unfold k pit quake; positivity,t',d,?_⟩; have ht:Tendsto temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
 filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually (ge_mem_nhds (half_pos t')),ht.eventually (ge_mem_nhds uP)] with x hx v w N R A0 a' D u₁ u₂ j H hv hd h1 h2 Z X
 have h0:temp x≥0:= (Work.E09.temp_pos hx).le
 have hl:= mile_duly R H p hv Z a' w s.le h0 (hd.trans (Nat.le_mul_of_pos_right _ two_pos)) c e (show temp x+2*Real.exp (-(a*(d:ℝ)))≤e from (by linarith only [v,l])) X
 refine hl.weigh (Real.exp_monotone ?_) p
 have H' : ((N.val:ℝ)^4) ≤ sites N:= pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.le_mul_of_pos_right N.val (by decide : (0:ℕ)<2))) _
 let V:= sites N; have hp:0≤V:=zero_le_one.trans (sites_pos _)
 let Y:=flakes (temp x) Z.1
 apply (add_le_add_right (add_le_add_right (pang (d:=d) (r:=r) c p e Z (temp x)) _) _).trans
 let H₀:=(N.val:ℝ)^4; let Q:=quake r d 1*(45*6*C)*h^2
 change e^2*C*H₀+pit r d C*Y+ ((u₁+u₁+u₂)*V+ (f e*H₀+Q*Y))≤_
 change f e+e^2*C+3*e < ε at he'; change _≤ ε*V+(Q+pit r d C)*Y
 linarith only [mul_le_mul_of_nonneg_left H' (show 0 ≤ f e+ e^2*C from by unfold f; positivity),mul_le_mul_of_nonneg_right he'.le hp,mul_le_mul_of_nonneg_right h1 hp,mul_le_mul_of_nonneg_right h2 hp]
end YM.CF.Pannier.Damask.Capri
#print axioms YM.CF.Pannier.Damask.Capri.penalize
