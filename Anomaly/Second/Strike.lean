import Anomaly.Second.Sail
import YM.SU5.Exchange.Stack.Nest
import YM.SU5.Exchange.Stack.Racket
import YM.SU5.Exchange.Visa.Guide
import YM.SU5.Exchange.Seed.Transit
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Paige Vault Rill
open Kennel
variable {C B L:Side}{X Y:SOp C}{o:Seat C}{a b c d v s t Nτ:ℝ}{n l q j:ℕ}{p:BudgetPoint}
variable {h:Odd L.val}{H:Pricing j L h (Thread j)}{e:ℝ}(P:Grasp H B e)
open Sault Leaf Vow.TreasuryFog
local notation "N"=> mid C B
variable (R:GramM (mid C B))(K:Scree.Loom (mid C B))
variable {k m:ℝ} {V:phy (mid C B)} (u:Roof (mid C B) k e q K) (z:P.roundZ≤ (mid C B).val)
local notation "⚑r"=> funde j R.J.M (mid C B)
local notation "⚑P"=> Moire.bloom R.J.P
local notation "Ω_N"=> (Dwell N)
open QuadClock
-- next call. Shift at actual heat representation.Strong only rooted-on-keys
-- Can grant AFTER ancestor layout and any old Gram output works across deployments.
structure Hold (P:Grasp H B e)(R:GramM N)(K:Scree.Loom N)(q l:ℕ)(O:Seat (mid C B))(m s:ℝ)(V:phy N)(F:Bag (mid C B))(a b:ℝ):Prop extends Nest P R K q l O m s V F a b where
    rank(x:Orbit N):rank2 (giveB F x)
-- exactly works on all arities and literally same regulator pilot.Born column etc.
variable {O_: Seat (mid C B)}{F:Bag (mid C B)}
local notation "Mφ" G:max z:max=> (Oise.color_b R R.beta (R.F+G) R.slip z R.v)
-- explicit shape.Pay: attire via old energy in its *.Support* presentation
abbrev weaveOut {n₁:Side}(U T:Bag n₁): Bag n₁ := U+ regionW U T+ ((2:ℂ)⁻¹) • regionW (regionW U T) T
lemma profit_weave {n₁:Side}{U T:Bag n₁}{A:Support (More n₁)}(t:Barrage p q A m U (s+d+d) a b)(r:Sectoral p q T m (s+d) c) (hx:0 ≤ s)(w:0 < d) : let z:= 2*(spanV p.B*d⁻¹*a*c); let P':= z+(2:ℝ)⁻¹*(2*(spanV p.B*d⁻¹*z*c)); Barrage p q A m (weaveOut U T) s (a+ P') (b+P'):=by
 let Zt:=attireV_fee t r (add_nonneg hx w.le) w; let Zs:= attireV_fee Zt (r.lessR (le_add_of_nonneg_right w.le)) hx w
 intro z P'; let P:= (((t.lessR (d:=s) (by linarith)).plusR (Zt.lessR (by linarith))).plusR (Zs.swell ((2:ℂ)⁻¹)))
 rw [norm_inv,show ‖(2:ℂ)‖=(2:ℝ) by norm_num,add_assoc a,add_assoc b] at P; exact P
lemma weave_formula {n₁:Side}{U T:Bag n₁}{A:Support (More n₁)}(t:Barrage p q A m U (s+d+d) a b)(r:Sectoral p q T m (s+d) c) (hx:0 ≤ s)(w:0 < d)(x:Orbit n₁)(F:Dough (Dwell n₁))(z:ℂ)(v:giveB T x=z • 1+F.val): giveB (weaveOut U T) x=attire (giveB U x) F:=by
 let H₀:=attireV_fee t r (add_nonneg hx w.le) w
 have ht(V W:Bag n₁):giveB (V+W)=giveB V+giveB W:=by simp_rw [giveB,Pi.add_apply, sum_add_distrib]
 let y:ℂ:=2⁻¹; have hk(V:Bag n₁):giveB (y • V)= y • giveB V:=by simp_rw [giveB,Pi.smul_apply,smul_sum]
 unfold weaveOut; rw [ht,ht,hk,attireV_formula H₀ r,attireV_formula t r]; simp only [Pi.add_apply,Pi.smul_apply]; unfold cBump; simp only [Pi.sub_apply,Pi.mul_apply, v]
 have hw (X:FC (Dwell n₁)):X*(z • 1+F.val)-(z • 1+F.val)*X=bump X F.val:=by rw [mul_add,add_mul,(Commute.one_right X|>.smul_right z).eq]; unfold bump; abel
 unfold attire; rw [hw,hw]; unfold y; simp only [← Complex.ofReal_ofNat (n:=2), ← Complex.ofReal_inv, Complex.coe_smul]; -- rfl ?
lemma pilot_kindle (G:RegBudget N)(F':ForceBudget N)(x:Orbit N)(h:IsStarProjection (spar j R.J.M (K x)))(v:Wave (Dwell N)): pilotH P (Mφ G F') K x h v= pilotH P R K x h (acts (exp (exponentL R.p G x.1)).val v):=by
 let Z:=exponentL R.p R.F x.1+exponentL R.p R.slip x.1; let W:= exponentL R.p G x.1
 change (Complex.exp (R.betaL K x)) • (Sault.ballL _ _) (acts (exp (exponentL R.p (R.F+G) _+ _)).val v)= (Complex.exp (R.betaL K x)) • (Sault.ballL _ _) (acts (exp Z).val _)
 rw [(TreasuryFog.exp_gain _ _ 0).2,add_right_comm _ W]; letI: NormedAlgebra ℚ (Cipher N):= NormedAlgebra.restrictScalars ℚ ℂ _
 rw [exp_add]; exact congrArg ((Complex.exp (R.betaL K x)) • ·) (congrArg (fun v=> Sault.ballL (nursery _ h) (relV P R.J (K x)) v) (act_mul ..))
variable {LQ:Bag (mid C B)}
lemma Hold.uplift (t:Hold P R K q l O_ m (s+d+d) V F a b)(G:RegBudget N)(F':ForceBudget N)(y:ℂ)(r:Sectoral R.p q LQ m (s+d) c)(hy:∀ i:Orbit N,FleetS R.p.threshold i.1 → giveB LQ i=y • (1:FC (Dwell N))+(exponentL R.p G i.1).val)(hu:0 ≤ s)(v:0 < d) : let z:= 2*(spanV R.p.B*d⁻¹*a*c); let Z:= z+(2:ℝ)⁻¹*(2*(spanV R.p.B*d⁻¹*z*c)); let A:=weaveOut F LQ; let X:=Mφ G F'; Barrage R.p q (grooveB l R.p O_) m A s (a+Z) (b+Z) ∧ ∀ i:Orbit N,FleetS R.p.threshold i.1→∀ h:IsStarProjection (spar j R.J.M (K i)),∀ v:Wave (Dwell N), pilotH P X K i h (acts (∑ t:Aura N,A t i) v)= acts (V i) (pilotH P X K i h v):=by
 intro t' u Bucket R'; refine ⟨profit_weave t.pouch r hu v,?_⟩; intro i u h w
 let Z:=exponentL R.p G i.1; let Pq:= (acts (exp Z).val w)
 have he:giveB Bucket i=attire (giveB F i) Z:= weave_formula t.pouch r hu v i Z y (hy i u)
 have hp: acts (exp Z).val (acts (giveB Bucket i) w)= acts (giveB F i) Pq :=by
    rw [he, ←act_mul,attireExp _ _ (t.rank i),act_mul]
 rw [pilot_kindle P R K G F' i h _,pilot_kindle P R K G F' i h w, ←(show giveB Bucket i=_ from Finset.sum_apply ..)]
 rw [hp,show giveB F i=_ from Finset.sum_apply ..]; exact t.science i h _
#print axioms Hold.uplift
lemma glow_rank {m:Type*}[LinearOrder m][Fintype m]{X:FC m}{T:Dough m}(h:rank2 X): rank2 (attire X T):=by
 have hu : rank2 (bump X T.val):=by intro i j k; rw [h T i j]; simp [bump]
 have hz: rank2 (bump (bump X T.val) T.val):=by intro i j k; rw [h T T i]; simp [bump]
 show rank2 (_+_) -- real smul
 refine Leaf.σX _ _ (Leaf.σX _ _ h hu) ?_; rw [← Complex.coe_smul]; exact Leaf.ψX _ _ hz
variable {k':ℝ}
include u z
lemma grab_hold (w:R.slip=0)(hs:0 ≤ s)(hd:0 < d)(hz:Fence ⚑r ⚑P K R.p q l O_ m (s+d+d) V a b) (hp:Sectoral R.p q (scald R.p (Ione.head_L R.F)) m (s+d) c) : let t:=2*(spanV R.p.B*d⁻¹ * a*c); let Z:=t+(2:ℝ)⁻¹*(2*(spanV R.p.B*d⁻¹*t*c));∃ F:Bag (mid C B),Hold P R K q l O_ m s V F (a+Z) (b+Z):=by
 obtain ⟨J,Q,T⟩:=hz.stock; obtain ⟨F,p,h⟩:= Q.ticket; let U:=tailor R.p R.F F
 have ht(x:Orbit N): JointJ (spar j R.J.M (K x)) (R.J.P.den (K x)) 0 (V x) (giveB F x):=by
    have he:=T x; rw [Moire.bloom_P,h] at he; exact he
 refine ⟨U,⟨tailor_price R.p p hp hs hd,?_⟩, fun x=>?_⟩; swap; · unfold U; rw [tailor_at R.p p hp hs hd x]; exact glow_rank (ht x).rank
 intro x hx A; let V':=K x; let L:= nursery _ hx; let v₁:= ballL L (relV P R.J V')
 have hv: exponentL R.p R.slip x.1=0:=by rw [w]; simp [exponentL,numbE]
 let G:= exponentL R.p R.F x.1; let y:= Complex.exp (R.betaL K x)
 have hy(p':Wave (Dwell N)):pilotH P R K x hx p'= y • v₁ (acts (exp G).val p'):=by
    change y • v₁ (acts (exp (G+ exponentL R.p R.slip x.1)).val p')=_
    rw [hv,add_zero]
 let Fk:= acts (exp G).val A; have hh: acts (V x) (v₁ Fk)=v₁ (acts (giveB F x) Fk):= (ht x).sends hx _ (Spire.sea_g z V' (u.paid x) R.J.M) Fk
 rw [hy,hy,map_smul, ←show giveB U x=_ from Finset.sum_apply ..,(show giveB U x=attire (giveB F x) (exponentL R.p R.F x.1) from tailor_at R.p p hp hs hd x),←act_mul,attireExp _ _ (ht x).rank,act_mul,hh]
#print axioms grab_hold
end YM.CF.Swell
