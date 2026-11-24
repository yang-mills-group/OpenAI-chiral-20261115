import GaugeFieldConstruction.LehuaImprovedMars
import GaugeFieldConstruction.IvyMajorL
/-!
 # Canonical tensor extension

 Need SAME normalization both moment & generator. Improvement of M7 obtains proper law, could a priori change principal+mixing even in the given normalization. Need re-test. Cannot assume no order five mixing with the mixed leg! Four-by-four Ward equalities not S-conservation all Grades. We buy a smaller separator using div and translation tests together. Only requires U4 EXTERNAL; so smells live in T_S2.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C) (Y:AreaQc S)
namespace FirstPackMars
open Wick Mirror Invoice Raster
variable (H:FirstPackMars p Y) (G:NSF.Table.Hierarchy (BellTableMars p Y)) (W:Blush S atTop u)
local notation "l₄"=> Calibration.lift four
lemma StonyRainΛ (F:Axis→ΧiMars) (v:UV five)(hv:v=∑ i:Axis,Calibration.deriv i (F i))
 (h:∀ (b: ΧiMars)(f: Foil), silky (l₄ b) v f.p=0): v=0:=by
 let q:=shells five v
 have he(b:ΧiMars): couples (shells four b) q=0:=by
    rw [show shells four b=shells five (l₄ b) from (LinearMap.congr_fun (shell_lift four) b).symm]; exact empt (h b) -- tune
 have hq:q=∑ i:Axis,Calibration.P i (shells four (F i)):=by
    unfold q; rw[hv,map_sum]; exact sum_congr rfl fun i _=> LinearMap.congr_fun (scene i) (F i)
 have hf (i:Axis): couples (night (Calibration.P i (shells four (F i)))) q=0:=by
    rw[time_P,Mirror.price]; cases clockbit: Mirror.clock i <;> simp only [pay_true,pay_false,map_neg,LinearMap.neg_apply, left_leg,he,map_zero,neg_zero] -- tune
 by_contra! hp; have hu:= mirror_positive five v hp
 have hh : couples (shells five (Calibration.shade five (spinFrame five mirror v))) (shells five v)=0:=by
    rw [← Mirror.price]; change couples (night q) q=0; nth_rw 1 [hq]; rw[map_sum, map_sum,LinearMap.sum_apply]; exact sum_eq_zero fun i _=> hf i
 rw [hh,map_zero] at hu; simp at hu
lemma StoutRainΛ (A:ΧiMars)(a:Axis)(h:∀ (b:ΧiMars)(f:Foil), silky (l₄ b) (Calibration.deriv a A) f.p=0): Calibration.deriv a A=0:=by
 apply StonyRainΛ (fun i=> if i=a then A else 0) _ _ h
 rw [sum_eq_single a]; simp
 · intro b _ u; simp[u]
 simp
open Row Record Flux.One RawBank -- need Scope.Nat
-- detector.Stages.Costs, ℂ.Basis
variable {σ:ℕ} {Q:ℕ→Carat}
private abbrev ΡsigmaΛ:= Foil × Axis × ΧiMars
private abbrev ΡlambdaΛ:= Foil × Axis × ΧiMars × ΧiMars
private abbrev ΨpaperΛ:= ΡsigmaΛ ⊕ ΡlambdaΛ
private def stripe4posΛ : SymT→ₗ[ℂ] ΨpaperΛ→ℂ:= by
    apply LinearMap.pi; intro v; cases v with
    | inl p=> exact survey p.1 ∘ₗ silky (l₄ p.2.2) ∘ₗ LinearMap.proj p.2.1 ∘ₗ OneW.subtype ∘ₗ divergence
    | inr p=>
       let a:=l₄ p.2.2.1; let b:=l₄ p.2.2.2
       let f:=p.1
       exact ∑ i:Axis,∑ j:Axis,audition a b (Fathom.perm flip_last (testcut (Payroll.ticket p.2.1) f.p f.a f.u.cared i j)) ∘ₗ LinearMap.proj (ordered i j) ∘ₗ SymT.subtype
private lemma stripe4iΛ (a:SymT)(q:ΡsigmaΛ): stripe4posΛ a (.inl q) = silky (l₄ q.2.2) ((divergence a).val q.2.1) q.1.p:=rfl
private lemma stripe4jΛ (a:SymT)(q:ΡlambdaΛ): stripe4posΛ a (.inr q) = freight q.1 (Payroll.ticket q.2.1) a (l₄ q.2.2.1) (l₄ q.2.2.2):=by
 -- unpack prove term
 change (∑ i:Axis,∑ j:Axis,audition (l₄ q.2.2.1) (l₄ q.2.2.2) (Fathom.perm flip_last (testcut (Payroll.ticket q.2.1) q.1.p q.1.a q.1.u.cared i j)) ∘ₗ LinearMap.proj (ordered i j) ∘ₗ SymT.subtype) a=_
 rw [LinearMap.sum_apply]; apply sum_congr rfl; intro i _; rw[LinearMap.sum_apply]; exact sum_congr rfl (fun j _=>shiftTag ..)
include W in
private lemma stripe4inΛ: Function.Injective stripe4posΛ:=by
 apply (detect _).mpr; intro x h
 have A: x∈ Conserved:=by
    change divergence x = 0; apply Subtype.ext; ext1 j; exact StonyRainΛ (fun i:Axis=>pens x i j) _ (component_div x j) (fun b f=> h (.inl (f,j,b)))
 have B:=supply.surjective ⟨x,A⟩
 obtain ⟨a,w⟩:=B
 let M:= atp (Calibration.deriv 0)
 have hp: M x=0:=by
    ext1 i; change Calibration.deriv 0 (x.val i)=0
    let k:=totalIx (1:Bundle); have hg: Calibration.deriv 0 (x.val i)= packΘ a.1 a.2 (basis 0) (k.val.val i):=by
        have hu:= pure_x a 1 0 i
        rw [mul_one,show (totalIx a).val=x from congrArg Subtype.val w] at hu; exact hu
    refine StoutRainΛ _ _ (fun b t=>?_); rw [hg]
    rw [← penned W,show (totalIx a).val=x from congrArg Subtype.val w]; rw[← stripe4jΛ x (t,0,k.val.val i,b)] -- tune
    exact h _
 exact bill_true _ (hp.trans M.map_zero.symm)

local notation "𝕋"=> SymT
private def toroΛ (Q:Carat)(t:SymT)(i j:Axis)(y z:ΧiMars) : Bond 3:= S.armed (prints (Q.t t)) (tie (lens Q five (l₄ z)) (lens Q five (l₄ y))) i j ∘ₗ Q.u.roll
private abbrev billΛ (Q:Carat)(A:ΡlambdaΛ)(i j:Axis): SymT→ₗ[ℂ]ℂ:=
    let X:=A.1; let t:= Fathom.testcut (Payroll.ticket A.2.1) X.p X.a X.u.cared i j
    (LinearMap.applyₗ (Q.u.roll t)) ∘ₗ (S.tagged (tie (lens Q five (l₄ A.2.2.2)) (lens Q five (l₄ A.2.2.1)))) ∘ₗ l₄ ∘ₗ LinearMap.proj (ordered i j) ∘ₗ SymT.subtype ∘ₗ Q.t.toLinearMap
private def stroke4pΛ (Q:Carat) : SymT→ₗ[ℂ] ΨpaperΛ→ℂ:= LinearMap.pi <| Sum.elim (fun p:ΡsigmaΛ=> survey p.1 ∘ₗ lunar S Q (l₄ p.2.2) ∘ₗ LinearMap.proj p.2.1 ∘ₗ OneW.subtype ∘ₗ left₃ L Q) (fun p:ΡlambdaΛ=> ∑ i:Axis, ∑ j:Axis,billΛ (S:=S) Q p i j)
private lemma stroke4iΛ (v:Carat)(A:SymT)(q:ΡsigmaΛ):stroke4pΛ (L:=L) v A (.inl q)= lunar S v (l₄ q.2.2) ((left₃ L v A).val q.2.1) q.1.p:=rfl
private lemma stroke4jΛ (v:Carat)(A:SymT)(q:ΡlambdaΛ): stroke4pΛ (L:=L) v A (.inr q) = delta (Payroll.ticket q.2.1) q.1.p q.1.a q.1.u.cared (toroΛ (S:=S) v A · · q.2.2.1 q.2.2.2):=by
 change (∑ i:Axis, ∑ j:Axis,billΛ (S:=S) v q i j) A=_; rw [LinearMap.sum_apply]; apply sum_congr rfl; intro i _; rw [LinearMap.sum_apply]; exact sum_congr rfl (fun j _=>rfl)

include W p in
private lemma stripe4outΛ : Scores ℂ atTop stripe4posΛ (fun k=> stroke4pΛ (L:=L) (u k)):=by
 intro j t; rcases j with j|j
 · rw[stripe4iΛ]; simp_rw [stroke4iΛ]; let V:= fun k=>LinearMap.applyₗ (R:=ℂ) j.1.p ∘ₗ lunar S (u k) (l₄ j.2.2) ∘ₗ (LinearMap.proj (R:=ℂ) j.2.1) ∘ₗ OneW.subtype; let H:=LinearMap.applyₗ (R:=ℂ) j.1.p ∘ₗ silky (l₄ j.2.2) ∘ₗ LinearMap.proj j.2.1 ∘ₗ OneW.subtype
   have ε:∀ (q:OneW),Dips ℂ atTop (fun k=>V k q) (H q):= fun _=> seen.mpr (W.pair ..)
   -- use explicit Dips
   have hp:Dips ℂ atTop (fun k:ℕ=> V k ((left₃ L (u k)) t)) (H (divergence t)):= trav ε (fun k:ℕ=> left₃ L (u k) t) (divergence t) (downstairs L W.toViews t)
   exact seen.mp hp
 rw [stripe4jΛ]; simp_rw [stroke4jΛ]
 exact tripleFlux W j.1 (Payroll.ticket j.2.1) (l₄ j.2.2.1) (l₄ j.2.2.2) (fun _=>t) t (fixed t)
local notation "Δ_"=> Fathom.delta
abbrev ΑtraDivΛ (T:SymT):Prop:=∀ (a:Axis)(b:ΧiMars)(f:Test 2),(∑ i:Axis, Fathom.paid front i (S.spot (other (l₄ b)) front (l₄ (pens T i a))) f)=0
abbrev ΑtraMarkΛ (T:SymT):Prop:= ∀ (a:Axis)(x y:ΧiMars)(f:Test 2)(J:Bulb)(q:Works J f front), Δ_ (Payroll.ticket a) f J q.cared (S.armed (prints T) (tie (l₄ y) (l₄ x)))=0
include W p in
lemma NobodyBlankΛ (T:SymT)(h: ΑtraDivΛ (S:=S) T)(v: ΑtraMarkΛ (S:=S) T): T=0:=by
 obtain ⟨k,e⟩:= (insight (stripe4inΛ W) (stripe4outΛ p W)).1.exists
 let Q:=u k; apply Q.t.symm.injective; rw [map_zero]; apply (detect _).1 e (Q.t.symm T); rintro (x|t)
 · rw [stroke4iΛ]; change lunar _ Q _ _ _=_; rw [sv]; simp only [map_sum, LinearMap.sum_apply]; unfold pens; let A:=Q.t.symm T
   change (∑ i:Axis,lunar S Q _ (levelP P Q i (A.val (ordered i x.2.1))) x.1.p)=_; let v':= l₄ x.2.2; let Ω:=(Q.G four).c x.2.2
   have he(i:Axis): lunar S Q v' (levelP P Q i (A.val (ordered i x.2.1))) x.1.p= Q.κ • Fathom.paid front i (S.spot (other (l₄ Ω)) front (l₄ (pens T i x.2.1))) ((Q.u).roll x.1.p):=by
      rw[lucid,vert,show (Q.G five).c v'=l₄ Ω from Q.include_ .., map_smul, LinearMap.smul_apply,← Q.t_pay, show Q.t A=T from Q.t.apply_symm_apply T,L.money]
   change (∑ i:Axis,lunar S Q v' (levelP P Q i (A.val (ordered i x.2.1))) x.1.p)=_; rw [sum_congr rfl (fun i _=>he i),←Finset.smul_sum,h,smul_zero]
 obtain ⟨f,i,a,b⟩:=t
 rw[stroke4jΛ]; change Δ_ _ _ _ _ (fun j x=>S.armed (prints (Q.t _)) (tie _ _) j x ∘ₗ Q.u.roll)=_
 rw [show Q.t _=T from Q.t.apply_symm_apply T]
 let X:=lens Q four a; let Y:=lens Q four b; let A':=S.armed (prints T) (tie (l₄ Y) (l₄ X)); rw [show lens Q five (l₄ b)=_ from Q.include_ four b,show lens Q five (l₄ a)=_ from Q.include_ four a]
 change delta _ f.p f.a f.u.cared (fun i j=> A' i j ∘ₗ Q.u.roll)=_
 have hv:= v i X Y (Q.u.roll f.p) (Q.u.band f.a) (Q.u.Works' f.u)
 change delta _ _ _ _ A'=0 at hv
 rw [Q.u.do_move i f.p f.a front f.u] at hv; exact (smul_eq_zero.mp hv).resolve_left (pow_ne_zero _ Q.nζ)
#print axioms NobodyBlankΛ
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
