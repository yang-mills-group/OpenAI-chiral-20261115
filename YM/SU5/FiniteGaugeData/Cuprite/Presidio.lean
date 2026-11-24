import YM.SU5.FiniteGaugeData.Drachma.Tanin
import YM.CF.Gall.Geld
import YM.SU5.FiniteGaugeData.Cuprite.Jersey
/-! # A heat account before height, ANY aperture. This is what lets us approach ANY tolerance without different phase or electing an increasingly enormous one Theory height.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 500000
set_option linter.flexible false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Window.Presidio
open Parcel.Tanin Fock Fock.Reduction Reduction.Hutch Reduction.Drama Reduction.Drama.Pack Reduction.Jersey -- tune resolution
open Next.Free Function Filter NormedSpace Lattice Laurent Bloch Wilson Precision Tree Finset Exterior
open Lat Rush Cube Scroll SU Peaks Dial Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Cour Fir Ember Aroma Cascade Gall
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {N : Side} {k:ℕ} {d b:ℝ}{M:Male}
set_option quotPrecheck false
local notation "Φ" => love N
local notation "Φ⁻" => (love N).symm
local notation "R"=> (spar k M (1:Bkg (More N)))
-- ° note Ireland
local notation "Θ"=> tickA N
local notation "Ξ"=> ampleR k N M
local notation "Θ'"=> spring (tickA N) (ampleR k N M)
variable (p:1≤k)
include p
lemma iceT: lit Θ':=by
 have hv: scaleQ N k M=Φ⁻ (spring (tickA N) (ampleR k N M)):= rfl; have he:= cold N k p M; rw [hv] at he; refine ⟨add_nonneg (mul_star_self_nonneg Ξ) (plus_P _ |>.one_sub.nonneg),?_⟩; rw [← StarAlgEquiv.apply_symm_apply (love N) Θ']; exact he.map Φ
lemma springMeter(M:Male): photo_ψ k N M=rueD (spring (tickA N) (ampleR k N M))/2:=by unfold photo_ψ galaZ Thera.OrbT; simp only [add_zero,mul_one]; rw [rueD,def_norm (iceT p).1]; unfold spring ampleR; ring -- scope N inferred implicit
abbrev sparseA(k:ℕ)(M:Male):Site N→Op (coneA Slot):= fun i=> edgeH Slot k M.val (mel i)
lemma year_inv : Φ⁻ Θ'⁻¹=subHub (sparseA k M)+(1-flatV Slot N):=by
 let A:=flatV Slot N; let X:=subHub (fun i=>shell k M.val (mel (N:=N) i) • bins Slot); let Y:=subHub (sparseA (N:=N) k M); have he:A=subHub (fun _: Site N=>bins Slot):=bin_hub.symm
 have hk(i:Site N):shell k M.val (mel i) ≠0:=div_ne_zero (fun h=> (noGhost (p:=mel i) (N:=M.val) (base_subset_realCube zone_pos (mel_h i)) (mel_away i)).ne' (congr_arg Complex.re h)) (mass_ne k _ M.property (base_subset_realCube zone_pos (mel_h i)))
 let L:=Φ⁻ Θ'; let Z:= Y+(1-A); have hG (U V:Site N→Op (coneA Slot)): subHub U*subHub V=subHub (fun i=> U i*V i) := lung (Equiv.refl _) U V
 have h: L*Z=1:=by
   have ht:X*Y=A:=by unfold X Y; rw [hG]; simp_rw [sparseA,edgeH,Matrix.mul_smul,Matrix.smul_mul,binsSq, inv_smul_smul₀ (hk _),he]
   have hu: X*A=X:=by unfold X; rw [he,hG]; simp_rw [Matrix.smul_mul,binsSq]
   have hv:A*Y=Y:=by unfold Y; rw [he,hG]; simp_rw [sparseA,edgeH,Matrix.mul_smul,binsSq]; rfl
   rw [show L=X+(1-A) from iceQ N k p M]; unfold Z; rw [add_mul,mul_add,mul_add,ht,mul_sub,sub_mul (1:Cab Slot N) A Y,hu,hv,mul_one,one_mul,sub_self,sub_self,mul_sub,mul_one,sub_mul 1 A A,one_mul,show A*A=A from flatA.1]; abel
 apply (love N).injective; change Φ (Φ⁻ ((spring Θ Ξ)⁻¹))=Φ Z; rw [StarAlgEquiv.apply_symm_apply]; apply inv_red (iceT p); rw [← show Φ L=Θ' from StarAlgEquiv.apply_symm_apply ..,←map_mul,h,map_one]
omit p
private abbrev fluid(X:Op (Single N)) := ∃ A:Site N→Op (coneA Slot), Φ⁻ X=subHub A
private lemma fluidM {A B:Op (Single N)} (p:fluid A)(h:fluid B): fluid (A*B):= by obtain ⟨X,e⟩:=p; obtain ⟨Y,q⟩:=h; exact ⟨fun i=>X i * Y i,by rw [map_mul,e,q]; exact lung (Equiv.refl _) X Y⟩ -- target has `_` use metav
private lemma fluidT {A:Op (Single N)} (p:fluid A): fluid (star A):=by obtain ⟨X,e⟩:=p; exact ⟨fun i=>star (X i),by rw [map_star,e]; exact subhub_star _⟩
lemma trace_earn(A:Op (Single N)): TrR (Φ⁻ A)=TrR A:=by
 let e:=Tulip.helix N; have hp(j:Tx N Slot): (Φ⁻ A) j j= A (e.symm j) (e.symm j):=rfl
 unfold TrR Matrix.trace; simp_rw [Matrix.diag_apply,hp]; exact congrArg Complex.re (Equiv.sum_comp e.symm (fun i=>A i i))
private lemma light_year(A:Site N→Op (coneA Slot))(x:Site N)(k:coneA Slot): subHub A (x,k) (x,k)= ((N.val:ℂ)^4)⁻¹ * (∑ i:Site N,A i k k):=by
 let U:=spatialU N Slot; have h(i:Site N): Fourier N x i *star (Fourier N x i)= ((N.val:ℂ)^4)⁻¹:=by unfold Fourier; simp only [Matrix.of_apply,star_div₀]; rw [div_mul_div_comm, mul_comm (frequency i x),frequency_unit]; unfold normF; simp only [star_pow,star_natCast,one_div]; ring
 let C:=jump (Equiv.refl (Site N)) A; unfold subHub hub; rw [twist_formula]; change (U.val*C*star U.val:Cab Slot N) (x,k) (x,k)= _; rw [Matrix.mul_apply]; unfold Tx; rw [Fintype.sum_prod_type, mul_sum]; apply sum_congr rfl; intro i _
 have hy (j:Site N)(v w:coneA Slot): U.val (x,v) (j,w) = if v=w then Fourier N x j else 0:=by simp only [U,spatialU,Matrix.kroneckerMap_apply,Matrix.one_apply,mul_ite,mul_one,mul_zero]
 have hh (l:coneA Slot): (U.val*C) (x,k) (i,l)=Fourier N x i * A i k l:=by
    rw [Matrix.mul_apply]; unfold Tx; rw [Fintype.sum_prod_type]; unfold C; simp only [jump_apply,Equiv.refl_apply,ite_mul,mul_ite,zero_mul,mul_zero,hy]; rw [sum_eq_single i]; · simp only [ite_true,sum_ite_eq,mem_univ]
    · intro j _ g; simp [g]
    simp
 rw [sum_eq_single k]; · rw [hh]; change _ * star (U.val _ _)=_; rw [hy,if_pos rfl,mul_right_comm,h]
 · intro j _ e; change _*star (U.val (x,k) (i,j))= _; rw [hy,if_neg e.symm,star_zero,mul_zero]
 simp
include p
private lemma fluidNico: fluid Θ'⁻¹:=by
 let A:=subHub (fun _:Site N=>bins Slot); let B:Site N→Op (coneA Slot):= fun _=>1; have he: subHub B - A=subHub (B-fun _=> bins Slot):=hubgap ..
 have h:1-A=subHub (B-fun _=>bins Slot):= by rwa [show subHub B=1 from unitHub] at he
 unfold fluid; rw [year_inv p,show flatV Slot N=A from bin_hub.symm,h]; exact ⟨_,hubsum (Equiv.refl _) _ _⟩
private lemma fluidLens: fluid (tickA N*(1-R)):=by
 have hh: Φ⁻ Ξ=subHub (fun i=> fuel Slot k M.val (mel i)):=by
    rw [show Ξ= grace k M (0:Dress N) 0 from ?_]; exact base_grace p M (0:Dress N) rfl
    unfold ampleR grace postR; simp [Crops,capT]
 unfold fluid; rw [mul_sub,mul_one]; change ∃_,Φ⁻ ((tickA N)-Ξ)=_; rw [map_sub,hh, plusInk N,StarAlgEquiv.symm_apply_apply,show flatV Slot N=_ from bin_hub.symm]; exact ⟨_,hubgap ..⟩ -- binder
private lemma figure (g:IsStarProjection R)(w:0≤b)(he:TrR Θ'⁻¹ ≤ b*(N.val:ℝ)^4): pointM (Single N) Θ R (Real.sqrt b) :=by
 let F:= Θ*(1-R); let H:=tangle Θ'; let T:=H*F; let P:=star T*T
 let hQ:= iceT (M:=M) (N:=N) p; have h:P=star F* Θ'⁻¹*F:= adams _ _ hQ; have hv:fluid P:=h ▸ fluidM (fluidM (fluidT (fluidLens p)) (fluidNico p)) (fluidLens p)
 let e:= Tulip.helix N; let C:=Fintype.card (Site N)
 have hv':TrR P ≤ b*(N.val:ℝ)^4:=by
    have hz:‖F‖ ≤1:= (needy (plus_P N) _).trans (g.one_sub.norm_le _); have hu:‖F*star F‖≤1:=by rw [CStarRing.norm_self_mul_star]; exact mul_le_one₀ hz (norm_nonneg _) hz
    have he':= (lit_inv hQ).1; rw [h,mul_assoc,TrR_comm, mul_assoc]; apply le_trans _ he; exact ((abs_le.mp (TrR_quote he' _)).2).trans (mul_le_of_le_one_left (TrR_nn he') hu)
 intro i
 let o:= (e i).2; let Z:=Φ⁻ P
 let f(j:Site N)(k:coneA Slot):= (Z (j,k) (j,k)).re
 let k₀:= P i i; let x:=k₀.re; have hZ(j:Tx N Slot): Z j j= P (e.symm j) (e.symm j):=rfl; have hθ: ∀ j:Tx N Slot,0≤(Z j j).re:=fun j=>by rw [hZ]; exact comp_pay (B:=P) (star_mul_self_nonneg T) _
 obtain ⟨W,hW⟩:= hv; have hr(j:Site N): f j o=x:=by
    have h: Z (j,o) (j,o)=Z (e i) (e i):=by unfold Z; rw [hW]; change subHub W (j,o) (j,o)=subHub W ((e i).1,o) ((e i).1,o); rw [light_year,light_year]
    unfold f x k₀; rw [h, hZ, Equiv.symm_apply_apply]
 have ht: TrR P=∑ j:Site N,∑ k:coneA Slot, f j k:=by rw [←trace_earn P]; change TrR (Z:Op (Site N × coneA Slot))=_; unfold TrR Matrix.trace; rw [Complex.re_sum,Fintype.sum_prod_type]; rfl
 have hc: x≤ b:= by
    have he: (N.val:ℝ)^4*x ≤ TrR P:=by rw [ht]; refine (sum_le_sum (f:=fun i:Site N=> x) (fun j _=> (single_le_sum (s:=univ) (f:=f j) (fun k _=> hθ (j,k)) (mem_univ o)).trans' (hr j).symm.le)).trans' ?_; simp
    nlinarith only [he,hv',pow_pos (nPos N) 4]
 have he':‖acts T (basisKet i)‖^2=x:= caible T i
 change ‖acts T (basisKet i)‖≤_; apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp; rw [he',Real.sq_sqrt w]; exact hc
-- trace density from curl standard integral up to N. no AP issue because n is even for sugars in Story.
omit p
private lemma sparse_k {x:Op (coneA Slot)} (_p:0≤b)(h:‖x‖≤b): TrR x ≤ Fintype.card (coneA Slot)*b:=by
 have ht := trace_diag x; refine (le_abs_self _).trans (ht.trans ((sum_le_sum (g:=fun _=> b) (fun i _=> (norm_entry _ _ _).trans h)).trans_eq ?_)); simp
include p
private lemma sugarShell: ∃ C:ℝ,0≤C∧∃ N₀:ℕ,∀ (N:Side)(M:Male),N₀≤N.val→Even N.val→TrR (spring (tickA N) (ampleR k N M))⁻¹ ≤ C*(N.val:ℝ)^4 :=by
 obtain ⟨C,h,N₀,hc⟩:= Cascade.sugar; obtain ⟨b,pb,hb⟩:= Cascade.chillY k p; let K:ℝ:= Fintype.card (coneA Slot);
 have hB : 0 ≤ K:= by unfold K; positivity
 let B:= b*(1+C); refine ⟨K*(B+1),by unfold B; positivity,N₀,fun N M k₀ g=>?_⟩; let h(i:Site N):= ‖bark i‖; let P(i:Site N):=b*(‖bark i‖^2)⁻¹; let F(i:Site N):=(shell k M.val (mel i))⁻¹; let T:=sparseA (N:=N) k M; let U:=subHub T; let V:=flatV Slot N
 have hp: IsStarProjection (bins Slot):= ⟨binsSq _,binsAdj _⟩; have hK(i:Site N): ‖T i‖≤P i:=by
    have he:T i= F i • bins Slot:=rfl; rw [he,norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg _) (hp.norm_le _)).trans (hb M N i)
 have hU: TrR U≤ K* (B*(N.val:ℝ)^4):=by
    have hT(i:Site N): TrR (T i) ≤ K*P i:= sparse_k ((norm_nonneg _).trans (hK i)) (hK i); unfold U TrR; rw [trace_hub,Complex.re_sum]; apply le_trans (sum_le_sum (fun i _=>hT i)); rw [←mul_sum]; apply mul_le_mul_of_nonneg_left _ hB
    have hx(i:Site N):P i ≤ b*(1+(‖bark i‖^3)⁻¹):=by
       have hu:0<h i:=(pinch_pos _).trans_le (Ember.torch i); apply mul_le_mul_of_nonneg_left _ pb.le; apply (le_total 1 (h i)).elim; intro p; exact le_add_of_le_of_nonneg (inv_le_one_of_one_le₀ (one_le_pow₀ p)) (by positivity); intro p; exact (inv_anti₀ (pow_pos hu 3) (pow_le_pow_of_le_one hu.le p (by norm_num :2≤3))).trans (le_add_of_nonneg_left (by norm_num)) -- tune
    apply (sum_le_sum (fun i _=>hx i)).trans; rw [← mul_sum,sum_add_distrib,sum_const, card_univ,site_card,nsmul_eq_mul,mul_one,Nat.cast_pow]; unfold B; linarith only [mul_le_mul_of_nonneg_left (hc N k₀ g) pb.le]
 let V':ℝ:= Fintype.card (Site N); have hv':V'=(N.val:ℝ)^4:=by unfold V'; rw [site_card,Nat.cast_pow]
 have hl: TrR (1-V)≤ V'*K:=by rw [TrR_sub,TrR_one,(show Fintype.card (Tx N Slot) = _ from Fintype.card_prod (Site N) (coneA Slot)),Nat.cast_mul]; exact sub_le_self _ (TrR_nn (show IsStarProjection V from ⟨flatA.1,flatA.2⟩).nonneg)
 rw [←trace_earn ((spring (tickA N) (ampleR k N M))⁻¹),year_inv p,TrR_add]; rw [hv'] at hl; linarith only [hl,hU]
-- gauge import and invitations in next
lemma meanA:∃ C:ℝ, 0≤C∧∃ N₀:ℕ,∀ N:Side, N₀ ≤ N.val → Even N.val →∀ M:Male, let Rq:= spar k M (1:Bkg (More N)); IsStarProjection Rq →let H:=spring (tickA N) (tickA N*Rq); lit H ∧ TrR H⁻¹ ≤ C*N.val^4 ∧ pointM (Single N) (tickA N) Rq (Real.sqrt C):=by
 obtain ⟨C,h,N,r⟩:= sugarShell p; refine ⟨C,h,N,fun M k g Rq t=>?_⟩; exact ⟨iceT p,r _ Rq k g,figure p t h (r _ Rq k g)⟩
end YM.CF.Window.Presidio
