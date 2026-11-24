import ForceSatin.Scepter
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit.SpringDay
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior RG Work.F06
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix
local notation "π" => Real.pi

open Matrix
abbrev snip (x:Momentum)(j:ℕ):= wedge j (fun i=>Complex.I*x i)
lemma lap(x:Momentum): (snip (-x) 1).transpose*snip x 1 + snip x 0*(snip (-x) 0).transpose = Fain x • (1:wireC):=by
 unfold snip; rw [crossed 0,sub_add_cancel]; unfold Fain prodM; congr 1; refine sum_congr rfl fun i h=> ?_; simp only [Pi.neg_apply]; ring_nf; norm_num
abbrev Herald (x: Momentum):wireC:= (Fain x)⁻¹ • 1
abbrev hornV (x:Momentum):orbC:= (snip x 1 * Herald x)*(snip (-x) 1).transpose
def regal (x: Momentum):orbC:= Vaunt x • hornV x
-- analytic estimates
section
variable {ι m n l:Type*}[Fintype m][Fintype n][Fintype l][DecidableEq m][DecidableEq n][DecidableEq l] {A A':ι→ℂ→Matrix m n ℂ} {B B':ι→ℂ→Matrix n l ℂ}
variable {p:ι→ℂ→Momentum} {Φ:Tax ι}{u v e:ℤ}
lemma morph (h:Actus Φ u A')(k:Actus Φ v B)(l':Actus Φ (u+e) fun i z=>A i z-A' i z)(g:Actus Φ (v+e) fun i z=> B i z-B' i z): Actus Φ (u+v+e) fun i z=> A i z*B i z-A' i z*B' i z :=by
 have hv:= Actus.comp l' k; have hp:= Actus.comp h g; rw [add_right_comm] at hv; rw [←add_assoc] at hp
 have he:= Actus.shift hv hp; simp only [Matrix.sub_mul,Matrix.mul_sub] at he; convert he using 1; ext i z x v; simp only [Matrix.sub_apply, Matrix.add_apply]; abel
variable (H:Move Φ p)
include H
lemma sincere(j:ℕ): Actus Φ 1 fun i z=> snip (p i z) j:= by intro a b; simp only [snip,wedge, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]; exact Act.finiteSum univ _ fun i _=> ((H.oneA i).lit _).mul (Act.anchor _ _)
lemma soaring(j:ℕ):Actus Φ 2 fun i z=> signal 1 j (p i z)-snip (p i z) j:=by
 intro i j'; simp only [signal,snip, Matrix.sub_apply,wedge,Matrix.sum_apply,Matrix.smul_apply,← sum_sub_distrib, smul_eq_mul,← sub_mul]; exact Act.finiteSum univ _ fun i _=> (signify H i).mul (Act.anchor _ _)
lemma filament {X:ι→Bed}{Q:Clip}{η C y:ℝ}(s:0<η)(v:0<C) (h:∀ i,(X i).covered η C) (L:ι→Side)(V:∀ i, Floor (X i) Q (L i) y C): Actus Φ 3 fun i z=> cliffMap (X i) (p i z)-Fain (p i z) • (1:wireC):=by
 let S(i) (z:ℂ):= snip (p i z) 1; let T(i) (z:ℂ):=snip (-p i z) 1; let K(i) (z:ℂ):= (X i).metric.read (p i z)
 let U(i):=(X i).metric; have he:Stock (fun _:ι=>1) (α:=fun _=> TypeFace 2) (β:=fun _=>TypeFace 2) U:= ⟨fun i=>zero_le_one,η,C,s,v,fun i=> by rw [mul_one]; exact (h i).2.1⟩
 have hz: Actus Φ 0 K:=by intro i j; exact (H.plunge ((price_reads he).tap i j))
 have ht: Actus Φ 1 fun i z=> K i z - 1:=by
    intro a b; refine H.freeze (f:=fun i z=> (U i).read z a b-(1:orbC) a b) (((price_reads he).tap a b).sub (Moderate.const _)) (fun i=>?_); rw [show (U i).read 0= 1 from (V i).starts,sub_self] -- tune
 let Z(i) (z):= mirage 1 1 (p i z); let V(i) z:= signal 1 1 (p i z)
 have hT:Actus Φ 1 (fun i z=> (T i z).transpose):= fun a b=> sincere (west H) 1 b a; have hx:Actus Φ 2 (fun i z=> Z i z-(T i z).transpose):=fun a b=> soaring (west H) 1 b a
 have hl :Actus Φ (1+0+1) (fun i z=> Z i z*K i z-(T i z).transpose*(1:orbC)):= morph (e:=1) hT hz hx ht
 simp only [Matrix.mul_one] at hl
 have ho :Actus Φ 3 (fun i z=> Z i z*K i z*V i z-(T i z).transpose*S i z):= morph (e:=1) hT (sprint H 1) hl (soaring H 1)
 have hp : Actus Φ 3 (fun i z=> signal 1 0 (p i z)*mirage 1 0 (p i z)-snip (p i z) 0*(snip (-p i z) 0).transpose):= morph (e:=1) (sincere H 0) (abroad H 0) (soaring H 0) (fun i j=> soaring (west H) 0 j i)
 simp only [←lap, cliffMap]; convert Actus.shift ho hp using 1; ext1 i; ext1 z; unfold Z K V T S; abel
end
#print axioms lap
-- keep Gauge. uses det loans from Hector through exponent 8 and at poles budget.B Extend inside complex at shift
structure crown (q:Clip)(σ η C:ℝ) where
 N:Side
 M:Bed
 L:Floor M q N η C
 a:M.covered σ C
 hn:Even N.val
variable {q:Clip}{σ η C:ℝ}
abbrev crownT (q:Clip)(σ η C:ℝ) : Lyra (crown q σ η C):=⟨crown.N,fun i=> rubyOff i.N,crown.hn⟩
abbrev wreath (u:(crownT q σ η C).Herb):Topaz q σ η C:=⟨u.era.N,u.era.M,u.era.L,u.era.a,u.era.hn,u.site,u.fresh,1,one_pos⟩
private lemma wreathCore{m:ℤ}(f:Topaz q σ η C→ℂ→ℂ)(h:Act (Topaz.G q σ η C) m f): Act (crownT q σ η C).Hint m fun i z=> f (wreath i) z:=by obtain ⟨a,b,u,t,h⟩:=h; exact ⟨a,b,u,t,fun i z hv=> h (wreath i) z hv⟩
variable (p:0<σ)(s:0<C)
include p s
lemma hornPromise (q:Clip)(η:ℝ)(a b:TypeFace 2): (crownT q σ η C).Singer 1 (fun i z=> Cov i.M z a b) (fun z=>regal z a b):=by
 let Φ:= crownT q σ η C
 have he (x:Axis): Actus Φ.Hint 0 (fun i z=> Cov i.era.M (Φ.amber x i z)):=fun a b=> wreathCore _ (costume p s x a b)
 refine ⟨fun a'=>?_,fun x=> ?_,fun x h=>?_,fun i=>?_,fun x y i ht _ _=>?_⟩
 · exact he a' a b
 · let U:=Φ.Hint; let u:=Φ.amber x; let M(i:Φ.Herb):=i.era.M; let K(i) z:= cliffMap (M i) (u i z); let f(i) z:= Fain (u i z); let R(i) z:= f i z • (1:wireC); let r(i) z:= Herald (u i z)
   have P (i:Φ.Herb) := i.era.L; let H:=Φ.amethyst x;
   have hp (i:Φ.Herb): aimRock q ^4 * (U.r i)^8 ≤ ‖(K i 0).det‖:=by unfold K u; rw [amber_dot]; exact det_fort i.era.L i.era.a p i.site i.era.hn i.fresh
   let V(i:Φ.Herb):ℂ:=(U.r i:ℂ)^(-2:ℤ); let Z(i) z:= V i • K i z
   have ht:Actus U 2 K:= fun a b=> wreathCore _ (route p s x a b)
   have hv:= Actus.scale ht (Actus.coin U (-2)); have hd:Act U 0 (fun i z=> (Z i z).det):= Actus.déterminant Z hv
   obtain ⟨c,hc,S⟩:= hd.stay (D:=aimRock q^4) (pow_pos (aimed _) _) (fun i=>(by
      have he:=hp i; have hP:=U.pos i; unfold Z; rw [Matrix.det_smul,norm_mul,norm_pow]; unfold V; rw [norm_zpow, Complex.norm_real,Real.norm_of_nonneg hP.le, show Fintype.card (TypeFace 1)=4 from (Fintype.card_congr axisEquiv).symm]; rw [zpow_zero,mul_one]; apply le_trans (b:=(U.r i ^ (-2:ℤ))^4*(aimRock q^4*(U.r i)^8)) ?_ (mul_le_mul_of_nonneg_left he (by positivity)); apply le_of_eq; field_simp))
   have hk: Actus U (-2) fun i z=> (K i z)⁻¹:= fun a b=> wreathCore _ (crystal p s x a b)
   let D:=aimRock q; have hD:= aimed q
   obtain ⟨l,t,L⟩:= H.knot.stay one_pos (emblem Φ x)
   have hR:Actus U (-2) r:= Actus.scale (fun i j=> Act.anchor U ((1:wireC) i j)) (H.knot.inv ⟨1,one_pos,emblem Φ x⟩) -- tune W defeq
   have hx:Actus U 3 fun i z=>K i z-R i z:= filament H p s (fun i=>i.era.a) (fun i=> i.era.N) P
   have hx': Actus U (-1) fun i z=> (K i z)⁻¹ - r i z:=by
      have he:= Actus.comp (Actus.comp hR (show Actus U 3 (fun i z=> R i z-K i z) from fun a b=> (by have he: Act U 3 _:= (hx a b).neg; simp only [Matrix.sub_apply,neg_sub] at he ⊢; exact he))) hk
      intro a b; apply (he a b).transfer; refine ⟨min c l,lt_min hc t,fun i z hv=> ?_⟩
      have hi:=U.pos i; have H₀: (Z i z).det ≠ 0:= norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (S i z (ball_subset_ball (min_le_left ..) hv)))
      have HF: f i z≠0:=norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (L i z (ball_subset_ball (min_le_right ..) hv))); rw [show Z i z= V i •_ from rfl,Matrix.det_smul] at H₀; have hS: IsUnit (K i z).det:= isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul H₀); dsimp only; rw [Matrix.mul_sub, Matrix.sub_mul,Matrix.mul_assoc (r i z) (K i z), Matrix.mul_nonsing_inv _ hS, Matrix.mul_one, show r i z * R i z=1 from ?_,Matrix.one_mul]; unfold r Herald R f; rw [Matrix.smul_mul,Matrix.one_mul,smul_smul,inv_mul_cancel₀ HF,one_smul]
   have H':Actus U 1 fun i z=> Cov (M i) (u i z)-hornV (u i z):=by
      exact morph (e:=1) (Actus.comp (sincere H 1) hR) (abroad H 1) (morph (e:=1) (sincere H 1) hk (soaring H 1) hx') (fun a b=> soaring (west H) 1 b a)
   have hS:Actus U 0 fun i z=> hornV (u i z):= Actus.comp (Actus.comp (sincere H 1) hR) (fun a b=> sincere (west H) 1 b a)
   have hM:= Actus.shift H' (Actus.scale hS (falcon H)); apply (show Actus U 1 (fun i z=> Cov (M i) (u i z)-regal (u i z)) from ?_) a b; simp only [sub_smul,one_smul] at hM; simp only [sub_add, sub_sub_self] at hM -- tune
   exact hM
 · change ContDiffAt ℝ ∞ (fun i=> Vaunt (tmap i)*(hornV (tmap i) a b)) x; have hp: ContDiff ℝ ∞ (Vaunt ∘ tmap):= Complex.contDiff_exp.comp fain_c.neg; apply hp.contDiffAt.mul
   simp only [hornV,Herald,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]; apply (raised x h).mul; apply ContDiff.contDiffAt; simp only [Matrix.mul_apply,Matrix.transpose_apply,snip,wedge,Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,Pi.neg_apply,tmap]; fun_prop
 · simp only [apex_zero]; simp [regal,hornV,Fain,prodM,Herald] -- tune
 obtain ⟨w,rfl⟩:= ht; rw [map_stem]; unfold Cov signal cliffMap mirage; simp only [signal,tripQ_stays,Row.periods,neg_add, ← reciprocal_negate] -- tune
#print axioms hornPromise
end YM.Regis.Circuit.SpringDay
