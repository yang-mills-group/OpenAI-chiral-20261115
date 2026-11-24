import YM.CF.Swell.Dune
import YM.CF.Swell.Fist
import YM.CF.Gas.Shop
import YM.CF.Chaff.Image
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
variable {N B m:Side}{r:ℕ}(k:ℕ) {a b c d t e:ℝ}
variable {P:BudgetPoint}{L:Scree.Loom N}(U:Roof N a e r L)(h:0<e)(hp:P.threshold≤ a)(hT:r+10≤ P.B)(hP:3 ≤ P.B)(hpκ:cipherK r≤ 5*P.B)(hx:HopeT e b t P.order)(hW:P.threshold ≤ t)
variable {S:Support (Cube.More N)}(o: Seat N)(p:o∈ S)(X:Scree.Hub N)(xP:X.val.1=o)(p': X.val.2=Lattice.halo P.B S)
open Gas Fief Push.AbsoluteSums Larch Chaff Vale
abbrev LenF(N:Side)(o:Seat N):= {i:Sa N//o∈i}
def bark_K (P:BudgetPoint)(S:LenF N o):Scree.Hub N:= ⟨(o,halo P.B S.val),halo_subset _ S.val S.property⟩
variable (V:SOp N)(A Tx:ℝ) (F:Sa N→ Raw (Openc (Cube.More N) e) (Single N))(W:Sa N→ Toll (Single N))(pφ:∀ i,Suite (badge _) (bail N e) (bail N e) i (W i) (F i)) (vφ:∀ i: Sa N,o∉ i→ W i=0)(gφ:tallyC A W≤ Tx)(xφ:∀ x: Openc (Cube.More N) e,V x.val=∑ S: Sa N,F S x)
variable (Tq:Ids N)(gA:0<A)(pMg:2*P.supportExponent*(Fief.tileN 1) ≤ A/2* P.B)
abbrev fit_σ (P:BudgetPoint)(S:LenF N o):=Swell.rent_Φ (P:=P) U h (bark_K o P S) (F S.val) Tq
abbrev utter(P:BudgetPoint):= Larch.sunY (univ: Finset (LenF N o)) (bark_K o P) (fit_σ U h o F Tq P) -- tune.Po
abbrev νmeta (P:BudgetPoint)(e:ℝ):=Real.exp (P.supportExponent*Fief.tileN 1)* reserveT P.power P.order 0 (e/2)
include U hp pφ vφ gφ xφ hT gA hW pMg hpκ hP hx
lemma horn_S(H:ℝ): IncX (fun _=>False) (utter U h o F Tq P) P H (νmeta P A * Tx) ∧ (∀ X:Scree.Hub N,X.val.1≠o→ utter U h o F Tq P X=0)∧ (∀ x: Orbit N,Rue.FleetS P.threshold x.1→flags P.threshold x.1=∅→ exponentL P (utter U h o F Tq P) x.1 = hollow (Matrix.trace (V (roller h U x).val))) :=by
 let Y(X:LenF N o):= bark_K o P X; let G(S:LenF N o):= S.val; let ω(S:LenF N o):= rGain P (G S) (W S.val); let T (S):= P.mass (Y S).val.2 (ω S); have he(X:LenF N o):PressB P (Y X) (fit_σ U h o F Tq P X) H (ω X):=helix_s U h hp hT hP hpκ hx hW _ o X.property (Y X) rfl rfl _ _ (pφ _) _ _
 let E:=utter U h o F Tq P; have hb(S):0 ≤ W S:= (pφ S).nonn; have hv:0 ≤ νmeta P A:=by unfold νmeta reserveT coin_n stilK; positivity
 have h0(Y:Sa N):0 ≤ledgerV (W Y):=sum_nonneg fun i _=>sum_nonneg fun j _=> hb Y i j
 have ha(X:LenF N o): T X ≤ νmeta P A * (rent A X.val*ledgerV (W X.val)):=by
    let G':=X.val; let w:= W G'; have ht:=hb G'; let C:= ledgerV w; have hp0:=h0 G'; let u:=P.supportExponent;
    by_cases hW:C=0; · change Real.exp _ * liftR _ _ _ C≤ _*( _*C); rw [hW]; simp [liftR,composeCost]
    have hz:Grove (terr _) G':=by obtain ⟨i,z,p⟩:=exists_ne_zero_of_sum_ne_zero hW; obtain ⟨j,l,t⟩:=exists_ne_zero_of_sum_ne_zero p; exact ((pφ G').expo i j|>.triggered t).1
    have hf:coverNumber 0 G'= G'.card:= Gas.zeroΩ G' hz
    let K:= surgeL P G' 0; let B:=reserveT P.power P.order 0 (A/2)
    have hg: liftR P G' 0 C ≤ (B * rent (A/2) G')* C:=by
       rw [show liftR _ _ _ _=liftR P G' 0 1*C from ?_]; swap; · unfold liftR composeCost; ring
       refine mul_le_mul_of_nonneg_right ?_ hp0
       have hp:=coinPay (k:=0) P G' (A/2) (by positivity); rw [hf] at hp; exact (le_mul_of_one_le_left (by unfold liftR composeCost surgeL; positivity) (rootA P o G' 0 X.property)).trans hp
    let V:=Lattice.halo P.B G'; let N':=Real.exp (u*Fief.tileN 1); let A':= Dial.idrat (Cube.More N)
    have ht:Real.exp (u*coverNumber P.B V)≤ N'*rent (A/2) G':=by
       have he(s:Sa N):s.image A'.parent=s:=by rw [show A'.parent=id from funext fun z=>by nth_rw 1 [←glass z]; exact Ratio.embed_parent .., image_id]
       have hv:=fen A' G' P.B 1 P.B_pos A P.supportExponent gA P.exponent_pos.le (by change _≤_* (↑(1:ℕ):ℝ)*_; simp only [Nat.cast_one,mul_one]; exact pMg) hz
       rw [he,one_mul] at hv; exact hv
    let R:= rent (A/2) G'
    refine (mul_le_mul ht hg (show 0 ≤ liftR _ _ _ C from ?_) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).trans_eq ?_ -- HP meta
    · unfold liftR composeCost surgeL; positivity
    change (N'*R)* (B*R*C)= N'*B*(rent A G'*C); rw [show rent A G'=R*R from ?_]; ring
    unfold R rent; rw [←Real.exp_add]; congr 1; ring
 have hr: (∑ X:LenF N o,rent A X.val*ledgerV (W X.val)) ≤ Tx:=by
    refine le_trans ?_ gφ; let f(X:Sa N):=rent A X*ledgerV (W X); let X:= univ.image (fun t:LenF N o=> t.val); apply le_trans _ (sum_le_sum_of_subset_of_nonneg (s:=X) (subset_univ _) (f:=f) (fun i _ _=> mul_nonneg (rent_pos _ _).le (h0 i))); unfold X; rw [sum_image Subtype.coe_injective.injOn]
 refine ⟨Larch.feat_v univ Y _ ω P (νmeta P A*Tx) (fun i _=> he i) ?_, fun i g=> ?_,fun x z u=>?_⟩
 · intro i; refine le_trans ?_ (mul_le_mul_of_nonneg_left hr hv); rw [mul_sum]; exact (sum_le_sum (fun j v=>ha j)).trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> mul_nonneg hv (mul_nonneg (Real.exp_pos _).le (h0 _)))) -- t vs goal filter
 · funext v; unfold utter sunY; rw [Finset.sum_apply]; apply sum_eq_zero; intro j t; exact False.elim (g ((mem_filter.mp t).2 ▸ (show (bark_K o P j).val.1=o from rfl)))
 have he: exponentL P E x.1=∑ i:LenF N o,fit_σ U h o F Tq P i x.1:=by
    unfold exponentL E utter sunY; simp_rw [show ∀ (i:Scree.Hub N)(G:InkD N), numbE P.threshold i.val.2 G x.1=G x.1 from fun i G=>Set.indicator_of_mem (show x.1∈_ from Leaf.lush_K x z u _) _, Finset.sum_apply]; exact sum_fiberwise_of_maps_to (fun _ _=>mem_univ _) _ -- tune
 change exponentL P E x.1=_; rw [he]; have hk(S:LenF N o): fit_σ U h o F Tq P S x.1=hollow (spineH U h (F S.val) x):= sketch U h hp hT _ (Y S) rfl (W _) _ (pφ _) Tq x (Leaf.lush_K x z u _)
 simp_rw [hk]; rw [Chaff.drillL, xφ,Matrix.trace_sum]; unfold spineH; apply congrArg hollow
 -- exclude other. simple sum_bij
 let S:= univ.image (fun t:LenF N o=> t.val); refine Eq.trans ?_ (sum_subset (s₁:=S) (subset_univ _) ?_); -- tune S name
 · unfold S; rw [sum_image Subtype.coe_injective.injOn]
 intro i _ v; have hp:W i=0:=vφ i fun h=>v (mem_image.mpr ⟨⟨i,h⟩,mem_univ _,rfl⟩); rw [show F i (roller h U x)=0 from ?_,Matrix.trace_zero]; ext j k; apply norm_le_zero_iff.mp; exact ((pφ i).expo j k|>.bounded _).trans_eq (by rw [hp]; rfl)
end YM.CF.Swell
