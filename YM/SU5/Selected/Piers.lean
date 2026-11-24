import YM.SU5.Selected.Winding
/-!
# CP6. Analyticity of built Repertoire along a time-lane. Extend to explicit eligibility and complex time
  tube (interior). No deformation in other coordinates (might apply after choosing any
  other-axis viewpoint). Valuate whole tuples of slots. Keep full semigroup S and verify
  time continuation *also* secures this (same Mink time group).
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric NormedSpace
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy ContinuousLinearMap
open OS Semigroup Complex
open scoped Topology InnerProductSpace NNReal ENNReal
variable {Ii:Type*}{M:Mesh}{a:Axis}{H:Hilbert} (X: Repertoire Ii a M H)
namespace Repertoire
local notation "P"=> X.sky.track
local notation "S"=> glass X.sky (daylight M) X.sea X.glides
local notation "L"=> (P).Realm X.sky.list
local notation "F" x:max=> (S).F x
local notation "Ω"=> X.origin
local notation "U" x:max=> (S).U (diameter (a:=a) x)
variable (v:Ii→ Axis→ℝ)
noncomputable def migrate (i:Axis)(v:Ii→ Axis→ℝ) (x:Ii→ℝ): Ii→Axis→ℝ:=fun j=> Function.update (v j) i (x j)
@[simp] lemma migration(a:Axis)(v:Ii→Axis→ℝ) : migrate a v (fun i=> v i a)=v:= funext fun i=>Function.update_eq_self _ _
def fronts (i:Ii)(x:ℂ):ℂ:=x-((X.rise i).val:ℂ)
def expires (i:Ii)(x:ℂ):ℂ:=X.fronts i x+(((X.width i).val:ℝ):ℂ)
def Legit (l:List Ii)(z:Ii→ℂ)(b:Option ℂ) : Prop:=match l with
 | []=>True
 | i::l=> (∀ x:ℂ,b=some x→ (X.fronts i (z i)-x)∈ inside) ∧ Legit l z (some (X.expires i (z i))) -- recursion `Legit` ok?
local notation "V" x:max=> migrate a v x
-- normalized costs W same U along offsets; ignore real heights in feeding spatial moves (v full)
noncomputable def upCharge (l:List Ii)(v:Ii→Axis→ℝ)(z:Ii→ℂ)(b:Option ℂ) : (L).Op:=match l with
 | []=>1
 | i::l=> Option.elim b (1:(L).Op) (fun t:ℂ=> (S).F (X.fronts i (z i)-t)) * (X.clerk i (v i)).expense * upCharge l v z (some (X.expires i (z i)))
noncomputable def rigged (l:List Ii)(v:Ii→Axis→ℝ)(z:Ii→ℂ):ℂ:= inner ℂ X.origin (X.upCharge l v z none Ω)
lemma migrate_front (i:Ii)(x:Ii→ℂ): X.frontend ((V (fun i=> (x i).re)) i) i=(X.fronts i (x i)).re:=by simp [migrate,frontend,fronts]
lemma migrate_end (i:Ii)(x:Ii→ℂ): X.endline ((V (fun i=> (x i).re)) i) i=(X.expires i (x i)).re:=by simp [endline,expires,X.migrate_front v i x] -- simp match l notation?
lemma bmoves (l:List Ii)(z:Ii→ℂ)(b:Option ℂ) : X.Legit l z b ↔ X.Correct l (Pages true) (V (fun i=> (z i).re)) (b.map Complex.re):=by
 induction l generalizing b with
 | nil=> rfl
 | cons i l ih=>
   rw [Legit,Correct, X.migrate_end v i z, ih]; apply and_congr ?_ ?_
   · rw [X.migrate_front v i z]; rcases b with _|b <;> simp [Pages,inside,sub_pos] -- tune
   rfl
lemma worth_space (i:Ii)(z:Ii→ℝ): diameter (a:=a) ((V z) i) = diameter (a:=a) (v i):=by
 apply Subtype.ext; ext x; by_cases h:x=a; · subst a; exact Eq.trans (show (diameter (a:=x) _).val x=0 from (diameter (a:=x) _).property) (show (diameter (a:=x) _).val x=0 from (diameter (a:=x) _).property).symm -- implicit a cannot subst?
 change (diameter (a:=a) _).val x= _; rw [diameter_at ..,diameter_at ..]; exact Function.update_of_ne h ..
 all_goals assumption
lemma clerk_charge (i:Ii)(z:Ii→ℝ): (X.clerk i ((V z) i)).expense=(X.clerk i (v i)).expense:=by
 have ht(b k: Axis→ℝ)(t:diameter (a:=a) b=diameter k): diameter (a:=a) (-b)=diameter (-k):= neg_of _ _ t
 change (U _) ∘L _ ∘L (U _) = (U _) ∘L _ ∘L (U _); rw [ht _ _ (worth_space v i z), worth_space v i z]
where neg_of (b k:Axis→ℝ)(p:diameter (a:=a) b=diameter k) : diameter (a:=a) (-b)=diameter (-k):= by
        have he(z:Axis→ℝ): diameter (a:=a) (-z) = - diameter z:=by unfold diameter; exact map_neg ..
        rw [he,he,p]
lemma charge_real (l:List Ii)(u:Ii→ℝ)(b:Option ℝ)(h:X.Legit l (fun i=> (u i:ℂ)) (b.map Complex.ofReal)) : X.upCharge l v (fun i=> (u i:ℂ)) (b.map Complex.ofReal) = Ledger.rideBook (S) b none (l.map fun i=> X.clerk i ((V u) i)):=by
 induction l generalizing b with
 | nil=> cases b <;> exact Eq.symm ((S).eZero)
 | cons i l ih=>
   let x:Ii→ℂ:=fun i=> (u i:ℂ); have hf:X.frontend ((V u) i) i=(X.fronts i (x i)).re:= migrate_front X v i x; have hb:X.endline ((V u) i) i=(X.expires i (x i)).re:= migrate_end X v i x
   have hp : X.expires i (x i)=(X.endline ((V u) i) i:ℂ):=by rw [hb]; apply Complex.ext <;> simp [expires,fronts,x]
   have hx : (fun i=> (u i:ℂ))=x:=rfl; rw [hx] at h ⊢; rw [upCharge,List.map_cons,Ledger.rideBook, hp]; let k:=some (X.endline ((V u) i) i)
   have hw:X.Legit l x (k.map Complex.ofReal):=by change X.Legit l x (some ↑(X.endline ((V u) i) i)); rw [←hp]; exact h.2
   rw [show X.upCharge l v x (some (X.endline ((V u) i) i:ℂ))= _ from ih k hw,X.clerk_charge]
   refine congrArg (fun f:(L).Op=> f * _ * _) ?_; rcases b with _|b; · exact Eq.symm ((S).eZero)
   change F (X.fronts i (x i)-(b:ℂ)) = (S).E (Ledger.between (some b) (some (X.frontend ((V u) i) i)))
   have he : 0<(X.fronts i (x i)).re-b:=h.1 b rfl; let y:=(X.frontend ((V u) i) i-b).toNNReal
   have h0:0<y:=Real.toNNReal_pos.mpr (hf.symm ▸ he)
   change _=(S).E y; rw [show X.fronts i (x i)-(b:ℂ) = duration y from ?_, (S).roots_heat h0]
   apply Complex.ext
   · simp only [sub_re,duration,y,ofReal_re,hf,Real.coe_toNNReal _ he.le]
   simp [fronts,x,duration]
variable (h:∀ t:ℝ≥0,(S).E t Ω=Ω)
lemma board (l : List Ii)(u:Ii→ℝ)(b:X.Legit l (fun i=> (u i:ℂ)) none) : X.rigged l v (fun i=> (u i:ℂ)) = X.reading l (V u):=by
 unfold rigged; rw [show X.upCharge l v (fun i=> (u i:ℂ)) none= _ from X.charge_real v l u none b,on_the_books]; rfl
variable [Fintype Ii]
lemma charge_analytic (l:List Ii) (u:Ii→ℂ) (v':Option ((Ii→ℂ)→ℂ))(p:X.Legit l u (v'.map fun g=> g u))(h:∀ b,v'=some b→AnalyticAt ℂ b u) : AnalyticAt ℂ (fun z=> X.upCharge l v z (v'.map fun g=> g z)) u:=by
 induction l generalizing v' with
 | nil=>exact analyticAt_const
 | cons i l ih=>
    let f(z:Ii→ℂ):= X.fronts i (z i); let k(z:Ii→ℂ):= X.expires i (z i); have he:AnalyticAt ℂ f u:= (ContinuousLinearMap.proj (R:=ℂ) i |>.analyticAt u).sub analyticAt_const -- paren
    let g(z:Ii→ℂ):= X.upCharge l v z (some (k z)); have ht:AnalyticAt ℂ g u:= ih (some k) p.2 (by simpa using (show AnalyticAt ℂ k u from he.add analyticAt_const)); simp_rw [upCharge]; rcases v' with _|v'; exact AnalyticAt.mul (analyticAt_const (v:=(1 : (L).Op) * (X.clerk i (v i)).expense)) ht
    exact ((((S).localHeat _ (p.1 (v' u) rfl)).comp (f:=f-v') (he.sub (h v' rfl))).mul (analyticAt_const (v:=(X.clerk i (v i)).expense))).mul ht
noncomputable def cellM (l:List Ii) : Set (Ii→ℂ):= {x| X.Legit l x none}
lemma cellM_open (l:List Ii) : IsOpen (X.cellM l):=by
 let v:Ii→Axis→ℝ:=0; let f: (Ii→ℂ) → Ii→Axis→ℝ:= fun y=>migrate a v (fun i=> (y i).re); have hc:Continuous f:=by
    apply continuous_pi; intro i; apply continuous_pi; intro z; by_cases h:z=a; · subst z; simp_rw [f,migrate,Function.update_self]; fun_prop
    simp_rw [f,migrate,Function.update_of_ne h]; exact continuous_const
 rw [show X.cellM l=f ⁻¹' (X.highway l) from Set.ext (fun i=> X.bmoves v l i none)]; exact ((X.smooth_highway l).preimage hc)
lemma charge_holo (l:List Ii) : AnalyticOnNhd ℂ (X.rigged l v) (X.cellM l):=fun x h=> ((innerSL ℂ (E:=(L).space) Ω).analyticAt _).comp (((ContinuousLinearMap.apply ℂ (L).space Ω).analyticAt _).comp (X.charge_analytic v l x none h (by simp)))
-- exact Wick relative: reading on plan interior extends with edge group cost
lemma change_cost (t:ℝ≥0)(p:0<t)(u y:ℂ)(q:(y-u).re=t): F (y-u) = ((S).edge (-(y.im-u.im))).comp ((S).E t):=by
 rw [← (S).roots_heat p, (S).along (dur.mpr p)]; congr 1; apply Complex.ext; simp [duration,←q]
 simp [duration,sideways]
end Repertoire
-- thick operator: strip of real time norm. use factorization assumption
variable (S : OS.Semigroup H a)
lemma ante_strip (t s:ℝ≥0)(x:H.Op) : AnalyticOnNhd ℂ (fun z:ℂ=>S.F (duration t-Complex.I*z)*x*S.F (duration s+Complex.I*z)) {z|-(t:ℝ)< z.im ∧ z.im < s}:= by
 intro z hz; obtain ⟨p,h⟩:=hz; have hl:AnalyticAt ℂ (fun s:ℂ=> Complex.I*s) z:= analyticAt_const.mul (show AnalyticAt ℂ (fun z:ℂ=>z) z from analyticAt_id)
 refine (((S.localHeat _ (show 0<(duration t-Complex.I*z).re from ?_)).comp (f:=fun z=>duration t-Complex.I*z) (show AnalyticAt ℂ (fun z:ℂ=>duration t-Complex.I*z) z from analyticAt_const.sub hl)).mul analyticAt_const).mul ((S.localHeat _ (show 0<(duration s+Complex.I*z).re from ?_)).comp (f:=fun z=>duration s+Complex.I*z) (show AnalyticAt ℂ (fun z:ℂ=>duration s+Complex.I*z) z from analyticAt_const.add hl))
 all_goals simp only [add_re,mul_re,sub_re,duration,I_re,I_im, zero_mul,one_mul,ofReal_re] ; linarith
lemma ante_edge (t s:ℝ≥0)(x:H.Op)(z:ℝ)(p:0<t)(h:0<s) : S.F (duration t-Complex.I*(z:ℂ))*x*S.F (duration s+Complex.I*(z:ℂ)) = S.edge z*(S.E t*x*S.E s)*S.edge (-z):=by
 rw [show (duration t-Complex.I*(z:ℂ))=duration t+sideways z from ?_, show (duration s+Complex.I*(z:ℂ))=duration s+sideways (-z) from ?_]; rotate_left
 · unfold sideways; try push_cast
   ring
 · unfold sideways; push_cast; ring
 rw [← S.along (dur.mpr p),← S.either (dur.mpr h), S.roots_heat p,S.roots_heat h]; change S.edge z*S.E t*x*(S.E s * S.edge (-z))= _; simp only [mul_assoc]
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.Repertoire.board
#print axioms YM.SelectionAnalysis.Repertoire.charge_holo
#print axioms YM.SelectionAnalysis.ante_strip
