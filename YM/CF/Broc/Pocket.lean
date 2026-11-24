import YM.CF.Broc.Savant
/-! Transfer to rephasing on base lattice. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Broc
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Paige Phase Phase.Sample Brace Cube Peaks Tulip Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B K b N:Side}{j l q n:ℕ}{a e p d w:ℝ} (H: CoinG j l q n d a w)(g:Guide b e p d)(h:0<a)(hw:0<w)
include H g h hw
def chargeR'(n:ℕ)(a w:ℝ)(b:Side):= ((n:ℝ)*rateH a w b+(n:ℝ)*rateH a w b)
lemma cargo (T: Bars m b N)(hx:q≤N.val)(M:Male): Seat (foamK N e p) (fun x=> tread m b j l n M N T x.val.1 x.val.2.1 x.val.2.2) (rateK a b) (chargeR' n a w b) :=by unfold Bars at T; subst N; exact balanceJ H h hw g hx M
omit H g h hw
def pWorks(m B:Side)(e p:ℝ):Light (Site (Domain m B)) (Brace.Chord m B e p) (Funds m B) where
 frame:=terr _
 rel T x y:=Agrees T x.val.1 y.val.1 ∧ AgreeF T x.val.2 y.val.2
 expands _ _ h _ _ q:= ⟨fun i l r=>q.1 i (h l) (h r), q.2.less h⟩
 dress g x:=⟨(gauge g x.val.1,feast g x.val.2),x.property.1.cov _,slow_g _ _ _ x.property.2⟩
-- cast `x.property.1` depends typ

def rose(m B:Side)(e p:ℝ)(x:Brace.Chord m B e p): Plan (Index m) cloud:=rock m B x.val.1
abbrev fete(m B:Side)(e p:ℝ):=Sam (rose m B e p)
def lag(m B:Side)(e p:ℝ): Lit (rose m B e p) (pWorks m B e p) (complexA m B) where
 pollen p:= (pass m B p).toMeasurableEquiv
 level p:=rain_g m B p
 gauge x t g:=law_g m B x.val.1 t g
 phase:= by
   let X:= (↑(Brace.Chord m B e p)) ×Cue m; let H(x:X):=(x.1.val.1,x.2)
   let f :=fun x:Skin m B× Cue m=>law m B x.1 x.2
   change Continuous (f ∘ H); exact (show Continuous f from law_cont ..).comp ( (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
 spread:= complex_up m B
lemma popT (x:fete m B e p):ZeroF m B x.val.1.val.1 x.val.2:=law_rich m B _ _ x.property
lemma nick (T:Table m B)(x:Brace.Chord m B e p): Bank (rose m B e p x) (complexA m B T):=complex_down m B T
lemma nick_c(x y:Brace.Chord m B e p)(T:Table m B)(h:(pWorks m B e p).rel T x y)(t):sails (rose m B e p x) (complexA m B T) t=sails (rose m B e p y) (complexA m B T) t:=by
 apply prod_congr rfl; intro i g
 have ht: room m B i⊆ T:= (mem_filter.mp g).2; exact water_limit _ _ i t t (fun _ _=> rfl) (fun i a b=> h.1 i (ht a) (ht b))
def portCast(f:enoughV B e p)(k:0≤e)(x:fete m B e p): BinK (CSide m B) e p:= ⟨(x.val.1.val.1,starfish m B x.val.1.val.1 x.val.2,x.val.1.val.2),x.val.1.property.1,starK f k x.val.1.property.1 (popT x),x.val.1.property.2⟩
lemma shoph (f:enoughV B e p)(k:0≤e)(M:ℝ)(hk:0<a)(h:0≤M)(v:Duet m B)(p': Seat (foamK (CSide m B) e p) (fun x=>v x.val.1 x.val.2.1 x.val.2.2) a M): Seat (pWorks m B e p) (fun x=>song m B v x.val.1 x.val.2) (a/feeG (8*B.val)) (feeG (8*B.val)*M):=by
 let Y:= lag m B e p; let C:=portCast (m:=m) f k 
 let S:=feeG (8*B.val); have hp: 0<S:=by unfold S feeG; positivity
 have he:Continuous C:=by -- named issue
   apply Continuous.subtype_mk
   let P:=fete m B e p; let F:= fun i:P=> (i.val.1.val.1,i.val.2); let B':=fun i:P=> i.val.1.val
   have ht: Continuous B':=continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
   have hF: Continuous F:=(continuous_fst.comp ht).prodMk (continuous_snd.comp continuous_subtype_val)
   refine ((continuous_fst.comp ht).prodMk (Continuous.prodMk ?_ (continuous_snd.comp ht)))
   exact (starfish_c f k).comp_continuous (f:=F) hF (fun x=> ⟨x.val.1.property.1,popT x⟩) -- tune
 let F:=fun x:fete m B e p=> v (C x).val.1 (C x).val.2.1 (C x).val.2.2
 have Ht: Seat Y.botL F (a/S) (S*M):=by
   apply Seat.shop (c:=Y.botL) (b:=foamK (CSide m B) e p) (Φ:=foam _ (8*B.val)) (foams _ (mul_pos (by decide) B.property) _) p' C he h (div_nonneg hk.le hp.le) ((le_of_eq (div_mul_cancel₀ a hp.ne')))
   · intro T x y h; refine ⟨fun i a b=> h.1.1 i (foam_in _ _ T a) (foam_in _ _ T b), honor _ _ T h.2 h.1.1,h.1.2.less (foam_in ..)⟩ -- tune
   intro x t; let z:= (Y.botL.dress t x); refine ⟨t, Subtype.ext ?_⟩; let g:=starG f k x.val.1.property.1 (popT x) t
   exact Prod.ext rfl (Prod.ext g rfl)
 letI : LocallyCompactSpace ↑(Brace.Chord m B e p) := art_c
 have Hy:= Y.loot Ht (complexA m B) (fun x T=>nick T x) (fun _=>subset_refl _) (fun T x y h=> nick_c x y T h)
 convert Hy using 1; funext x
 unfold means song; apply integral_congr_ae; apply Eventually.of_forall; intro y;
 let z:ℝ:=law m B x.val.1 y; by_cases h:z≠0
 · unfold cream; dsimp only; rw [sampler_p F (x,y) h]; unfold herald; rw [Complex.real_smul]; rfl
 rw [not_not] at h; unfold cream herald; change (z:ℂ)* _= z • _; rw [h, zero_smul]; simp
end YM.CF.Broc
