import GaugeFieldConstruction.Cicero
import GaugeFieldConstruction.Plush
import GaugeFieldConstruction.Uber
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
set_option maxHeartbeats 240000
variable (I:Type)[LinearOrder I][Fintype I]
open SeasonH
variable (σ:I→Seat n)(V:Support (More n))(A:Pane n) (M:I→ Boke n I)(F:Fork n I)(r:ℝ)(v:stabH F)
variable (t:Finset I)(e:Vulcan I n)(S:Hubber n)(Q:Boke n I)
-- raw Lattice supports.Z cut zeta
namespace MintB
open Fren
variable (T: Sweep n)(P:BudgetPoint)(L:ℕ)(x:Scree.Hub n)
local notation "Ωv"=> boxA T
open SeasonH
variable (a b d u h c:ℝ)(i:I)
variable (C C' Υ:ℝ)(T':Torches n)
-- per plain label.Absorb.C pure at X0 use halo tags & pre-L. fix through p$ stroke order. b=2 in application (candidate X). Ensure p Lot SecX uses exponent<=2.
abbrev pap_B (y:Vulcan I n)(j:ℕ):= base_E y P h j
variable (pV:h>0)(g:Bouquet I i P b a h C T' σ (M i) C')
variable (va:0≤a)(hb:1≤ b)(h1:1≤h)(hR:0≤r)(pc:0≤c)(hv:0≤u)
variable (gP:buyV P d c)(y:0≤ d)(hd:2*d≤a)(sP:u*2*Yaw.χ (ThermalH L)≤↑P.B*d)(wZ:2*(ThermalH L*P.B)<(More n).val)
-- p.B ≥ 24. M.T pre cost.C R.
include hR va pc hv h1 hb gP y hd sP wZ
local notation "K0"=> b
local notation "Lr"=> Branch.rent
local notation "δ"=> c* Zell L u
abbrev builtE (z:Vulcan I n) : ℝ:= ∑ x:Scree.Hub n, pinH0 x u P.B*Lex_B σ z x L P {i} h
lemma Lip_far(e: Vulcan I n)(s:Linca P σ e)(t:e.keys=[i]): builtE I σ P L u h i e ≤ δ*wageL a b h e:=by -- argument order?
 let H:= lex_row I σ P L i e s t -- inspect
 let X: Scree.Hub n := ⟨(σ i,SpacePad L P σ e),mem_union_left _ (s.stamp.port i (by simp [t]))⟩
 have hy:marksY σ e L P {i}={X}:=H
 have hs:=ωHeld σ e X L P h a b d u c hd y hv gP sP wZ s pc {i} (hy.symm ▸ mem_singleton_self _) (zero_le_one.trans hb)
 rw [card_singleton,pow_one] at hs; unfold builtE Lex_B; simp_rw [hy,exp_Plate,card_singleton,Nat.cast_one,inv_one, one_mul,Finset.mem_singleton,mul_ite,mul_zero]; rw [Finset.sum_ite_eq', if_pos (mem_univ _)]
 apply le_trans _ hs; rw [mul_assoc]; refine le_mul_of_one_le_left (mul_nonneg (Real.exp_pos _).le (base0_E _ _ _ _ s _)) hb
omit hb hR va pc hv h1 gP y hd sP wZ -- syntax omit a not included? weaken
-- preserve compact price when puriform
local notation "qP"=> Pach (σ i)
include h1 hb hv hR
lemma Lip_cold (τ:24≤P.B)(z:Vulcan I n)(p:Linca P σ z)(t:z.keys=[i])(g:z.pure=true)(w:z.seat=Pach (σ i)):
 builtE I σ P L u h i z ≤ Real.exp u * bSalt P ((Pach (σ i)).card) * (Lite h z.val * z.won):=by
 let X:= Zhub (σ i); have he:SpacePad L P σ z=qP:=by unfold SpacePad; rw [w,g,if_pos rfl,union_empty] -- qP syntax need decl
 have hx:X.val.2=qP:=rfl; have hy:marksY σ z L P {i}={X}:=by
    refine Eq.trans (lex_row I σ P L i z p t) ?_; apply congrArg ({·}); exact Subtype.ext (Prod.ext rfl (show SpacePad L P σ z=X.val.2 from he))
 unfold builtE Lex_B; simp_rw [hy,exp_Plate,card_singleton,Nat.cast_one,inv_one,one_mul,Finset.mem_singleton,mul_ite,mul_zero]; rw [Finset.sum_ite_eq', if_pos (mem_univ _)]
 have ht: coverNumber P.B X.val.2≤1:= (Corona.cover_mono (D:=X.val.2) (X:=halo P.B {σ i}) (Corona.halo_mono τ (Subset.refl _)) _).trans (AnalyticBridge.CouplingShape.ballPaid ..)
 have hb:pinH0 X u P.B≤ Real.exp u:=Real.exp_monotone (mul_le_of_le_one_right hv (by exact_mod_cast ht))
 refine (mul_le_mul_of_nonneg_right hb (base0_E _ _ _ _ p _)).trans_eq ?_
 unfold base_E; rw [w]; ring
omit h1 hb hR hv
variable (γC γB:ℝ)(H:FumedH a b (Ekm n) F γC γB)(hwY:γC≥0)(uR:r=Γ0 P)(sK:stabH F)(hz:darkH F)
local notation "Vr"=>Vulcan I n
-- generic estimates for Core shape witnesses; purchase. suppress without #postnorm.
abbrev ExpectB(h k:ℝ):ℝ:=max 1 (h*k)

variable (τ:24≤P.B)

private lemma filterS{X A:Type}[AddCommGroup A](y:List X)(p:X→Bool)(f:X→A): Lee y f= Lee (y.filter p) f + Lee (y.filter fun i=>!p i) f:=by
 induction y with|nil=> simp [Lee]| cons a y ih=> simp only [List.filter_cons]; cases p a <;> simp only [Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte] <;> rw [consA y,ih] <;> try simp only [consA]; abel -- tune
variable (U:Fort P F)
include h1 hb H uR sK hv va hR hz τ pc gP y hd sP wZ hwY U
lemma worth_root (z: Vulcan I n)(p:Linca P σ z)(t:z.keys=[i])(u':z.pure=true)(v':z.seat=Pach (σ i)): Lee (growL F r [] z) (fun i0=> builtE I σ P L u h i i0) ≤ (Real.exp u*bSalt P ((Pach (σ i)).card) * max 1 (r^2) + δ *(r^2*γC/h^2))*wageL a b h z:=by
 let Q:= growL F r [] z
 let X:=durW r z; let Y(i0):= builtE I σ P L u h i i0; have hw:wageL a b h z≥0:=mul_nonneg (costsE ..) (WP_v _ _ _ (zero_le_one.trans hb) p.stamp.micro.1); have he:foli Q=[X]:=(Pure_P r F z hz).trans (if_pos u'); have ht:CostP σ P Q:=by unfold Q; rw [uR]; exact Fiscal σ P F [] U (fun i p=> by simp at p) z p -- requires Fort P F not available; add binder
 have hp':=grow_Stamp r F i z t sK; have hV:X∈ foli Q:=he.symm ▸List.mem_singleton.mpr rfl
 have hK: Lite h z.val *z.won≤ wageL a b h z:=by
    apply mul_le_mul_of_nonneg_left _ (costsE ..); unfold weightV; apply le_mul_of_one_le_left p.stamp.micro.1; exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) (one_le_pow₀ hb)
 change Lee Q Y ≤ _; rw [filterS _ (fun i:Vr=>i.pure),show Q.filter (fun i:Vr=>i.pure)=_ from he, consA, show Lee ([]:Boke n I) Y = (0:ℝ) from rfl,add_zero,add_mul]; apply add_le_add
 · have hm : X.val=z.val ∧ X.won≤ max 1 (r^2) * z.won∧ X.seat=z.seat:=by
      unfold X durW; split
      exact ⟨rfl,le_mul_of_one_le_left p.stamp.micro.1 (le_max_left ..), rfl⟩
      refine ⟨?_,?_,rfl⟩; rfl; exact (le_of_eq (show r*z.won*r=r^2*z.won from (by ring))).trans (mul_le_mul_of_nonneg_right (le_max_right ..) p.stamp.micro.1)
   have hx': X∈ Q:= List.mem_of_mem_filter hV; let u0:= Lip_cold I σ r P L b u h i hb h1 hR hv τ X (ht _ hx') (hp' i List.mem_cons_self X hx') ((List.mem_filter.mp hV).2) (hm.2.2.trans v')
   let C:= Real.exp u*bSalt P ((Pach (σ i)).card)
   have he:C≥0:=mul_nonneg (Real.exp_pos _).le (by unfold bSalt preFoot; positivity)
   apply le_trans u0; rw [mul_assoc C (max 1 (r^2)),hm.1]; apply mul_le_mul_of_nonneg_left _ he
   have hh:= mul_le_mul_of_nonneg_left hm.2.1 (costsE h z.val)
   apply hh.trans; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hK (zero_le_one.trans (le_max_left ..))
 let ξ:=Q.filter fun x=>!x.pure;
 have he':0≤ δ:=mul_nonneg pc (Real.exp_pos _).le; 
 have hU:Lee ξ (wageL a b h) ≤ (r^2*γC/h^2)*wageL a b h z:=by
    have ht0:= raw_pure (Ekm n) a b h r F γC γB z p.stamp.micro.1 hz u' H hR va (zero_le_one.trans hb)
    refine ht0.trans ?_; cases q:z.val with
    | none=> simp only [if_pos rfl,↓reduceIte,zero_mul]; exact mul_nonneg (by positivity) hw
    | some x=> simp only [if_neg (show some x≠ none from (Option.some_ne_none x))]; refine le_of_eq ?_; unfold wageL; rw [q]; change _= _* (h^2*_); have hh:h≠0:=(zero_lt_one.trans_le h1).ne'; field_simp
 refine le_trans (lea_p ξ _ (fun z=>δ*wageL a b h z) (fun j k =>?_)) ((lea_scale ..).le.trans ((mul_le_mul_of_nonneg_left hU he').trans_eq (mul_assoc ..).symm))
 let a': j∈ Q:= List.mem_of_mem_filter k; exact Lip_far I σ r P L a b d u h c i va hb h1 hR pc hv gP y hd sP wZ j (ht _ a') (hp' i List.mem_cons_self _ a')
abbrev tuneG(r γ:ℝ):= αR r (RadBill r γ 0) γ
lemma worth_floc (z:Vulcan I n)(p:Linca P σ z)(t:z.keys=[i]): Lee (growL F r [] z) (fun i0=> builtE I σ P L u h i i0) ≤ δ*tuneG r γC*wageL a b h z:=by
 let Q:=growL F r [] z; have he:=grow_Stamp r F i z t sK; have ht:CostP σ P Q:=by unfold Q; rw [uR]; exact Fiscal σ P F [] U (fun i p=> by simp at p) z p
 have hx := birth (Ekm n) a b h r F γC γB H [] 0 (show Puffion (Ekm n) ([]:Boke n I) from ⟨fun i v=> by simp at v,fun i v=>by simp at v⟩) (fun x=>le_rfl) hR va (zero_le_one.trans hb) h1 le_rfl hwY z p.stamp.micro.1 (σ i)
 have hvγ (i0:Vr)(v:i0∈ Q):costL a b h i0 (σ i)=wageL a b h i0:=by unfold costL wageL bil; rw [if_pos ((ht _ v).stamp.port i (he i List.mem_cons_self _ v|>.symm ▸ List.mem_cons_self))]
 let P':= Ekm n; have hA(j:FinV n): Aqua_D a b r F [] j (σ i)=0:=by simp [Aqua_D,frond,bil,Lee]
 -- however Tooth cost bound includes privH d at y even for singleton $ok$; better bound via all sum using tooth_pay directly.Mark property.No issue using privH fee c bound extra. aim αR Ω. calculate.
 have hw: Lee Q (wageL a b h) ≤ tuneG r γC * wageL a b h z:=by
    unfold Q Wosk.growL; cases hp:z.val with
    | none=> rw [consA,show Lee ([]:Boke n I) _= _ from (show Lee ([]:Boke n I) (wageL a b h)=0 from rfl),add_zero]; exact le_mul_of_one_le_left (mul_nonneg (costsE ..) (WP_v _ _ _ (zero_le_one.trans hb) p.stamp.micro.1)) (le_max_left ..)
    | some w=>
       obtain ⟨i,k⟩:=w; rw [mapA]; let Pz:= wageL a b h z; let T:= tuneG r γC; have hz:=p.stamp.micro.1; let t0 : Puffion (Ekm n) ([]:Boke n I):=⟨fun i v=>by simp at v,fun i v=>by simp at v⟩; have he:= tooth_pay (Ekm n) a b h r F γC γB H [] 0 t0 (fun i=>le_rfl) hR va (zero_le_one.trans hb) h1 le_rfl hwY i k
       have hf:0≤Pz:=mul_nonneg (costsE ..) (WP_v _ _ _ (zero_le_one.trans hb) hz)
       apply (lea_p _ _ (fun w:Vr=> r* Pz * weightV a b w) (fun w t=> ?_)).trans ((lea_scale ..).le.trans ((mul_le_mul_of_nonneg_left he (mul_nonneg hR hf)).trans ?_))
       · rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right (le_max_right ..) hf
       let v0:= tooth_s (Ekm n) a b r F γC γB H [] t0 hR i k |>.1 w t; have ht: Lite h w.val≤ Lite h z.val:=by rw [hp]; cases w.val; exact cursorE h h1 _; exact le_rfl
       apply (mul_le_mul ht (WP_pair a b r z w va (zero_le_one.trans hb) hR hz v0 w.val) (WP_v _ _ _ (zero_le_one.trans hb) (mul_nonneg (mul_nonneg hR hz) v0)) (costsE h z.val)).trans_eq; unfold Pz wageL; ring
 apply (lea_p Q _ (fun z=>δ*wageL a b h z) (fun z v=>Lip_far I σ r P L a b d u h c i va hb h1 hR pc hv gP y hd sP wZ z (ht _ v) (he i List.mem_cons_self z v))).trans; rw [lea_scale, mul_assoc (c*Zell L u) (tuneG r γC)]; exact mul_le_mul_of_nonneg_left hw (mul_nonneg pc (Real.exp_pos _).le) -- rw wrong assoc

-- complete $input estimate$
local notation "Δs"=> c*Zell L u
abbrev TaleX (a b h c d u v r η C A:ℝ)(k:ℕ):ℝ:= (Real.exp u*A * max 1 (r^2)+ c*Zell k u*(r^2*η/h^2))*(b* Real.exp (a*(49:ℝ)^4) *C)+ c*Zell k u*tuneG r η * (b*v)
variable (L0:List I)(h0:L0.Nodup)(w:stampK M L0)(κ:i∈L0)
include g w h0 κ
lemma cap_root : let Q:=Keeps F r M L0; let S:= fun x:Scree.Hub n=> entryW σ L P Q h {i} x
    ∑ x:Scree.Hub n,pinH0 x u P.B * S x ≤ TaleX a b h c d u C' r γC C (bSalt P ((Pach (σ i)).card)) L:=by
 intro Q S
 have hu:=Bloom_s I i P b a h C T' σ (M i) g (zero_le_one.trans hb)
 -- distribution
 have ht(x:Scree.Hub n): S x= Lee (topL F r [] (M i)) (fun z=>Lex_B σ z x L P {i} h):=by unfold S Q; rw [hail_B, sage_f I M F r i sK L0 h0 w, if_pos κ] -- Q
 let Q0(z:Vr):=Lee (growL F r [] z) (fun i0=> builtE I σ P L u h i i0)
 have hs(z)(t:z∈M i): z.keys=[i] := w i κ z t
 have hF: CostP σ P (M i):= Bloom_up I i P b a h C T' σ (M i) g |>.2
 let Z:=M i; let V:= foli Z; let V':=Slag I Z; let A:=Real.exp u*bSalt P ((Pach (σ i)).card) * max 1 (r^2)+Δs*(r^2*γC/h^2); have hg:0≤ A:= add_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (by unfold bSalt preFoot; positivity)) (zero_le_one.trans (le_max_left ..))) (mul_nonneg (mul_nonneg pc (Real.exp_pos _).le) (by positivity))
 simp_rw [ht, ←lea_scale,lea_sum]; unfold topL; rw [joinA]; change Lee Z Q0 ≤ _; rw [filterS Z fun z=>z.pure]; change Lee V Q0 + Lee V' Q0 ≤ _; unfold TaleX; apply add_le_add
 · refine (lea_p V _ _ (fun z t=>worth_root I σ F r P L a b d u h c i va hb h1 hR pc hv gP y hd sP wZ γC γB H hwY uR sK hz τ U z (hF z (List.mem_of_mem_filter t)) (hs _ (List.mem_of_mem_filter t)) (List.mem_filter.mp t).2 (hu.2.2.1 _ t))).trans ?_ -- tune. need sum.V factor
   change Lee V (fun x=> A*wageL a b h x) ≤ A*_ ; rw [lea_scale]; apply mul_le_mul_of_nonneg_left _ hg; apply hu.1.trans; have he:0≤C:=by have hx:0 ≤ b*Lr a qP*C:= le_trans (lea_n _ _ fun z v=> mul_nonneg (costsE ..) (WP_v a b _ (zero_le_one.trans hb) (hF z (List.mem_of_mem_filter (p:=fun x=>x.pure) v)).stamp.micro.1)) hu.1 ; exact nonneg_of_mul_nonneg_right hx (mul_pos (zero_lt_one.trans_le hb) (Real.exp_pos _)) -- tune nonneg.
   apply mul_le_mul_of_nonneg_right _ he; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hb); apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ va; exact_mod_cast (show (Pach (σ i)).card≤ 49^4 from (by simpa [Pach] using Corona.halo_size ({σ i}:Support (More n)) 24))
 refine (lea_p V' _ _ (fun z v=> worth_floc I σ F r P L a b d u h c i va hb h1 hR pc hv gP y hd sP wZ γC γB H hwY uR sK hz τ U z (hF z (List.mem_of_mem_filter v)) (hs _ (List.mem_of_mem_filter v)))).trans ?_
 rw [lea_scale]; exact mul_le_mul_of_nonneg_left hu.2.1 (mul_nonneg (mul_nonneg pc (Real.exp_pos _).le) (zero_le_one.trans (le_max_left ..)))
#print axioms cap_root
end MintB
end MastTin
end YM.CF.XGarden
end
