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
local notation "gR"=> funde j R.J.M (mid C B)
local notation "gP"=> Moire.bloom R.J.P
structure Nest (P:Grasp H B e)(R:GramM (mid C B))(K:Scree.Loom (mid C B))(q l:ℕ)(o:Seat (mid C B))(m s:ℝ)(V:phy (mid C B))(F:Bag (mid C B))(a b:ℝ):Prop where
    pouch: Barrage R.p q (grooveB l R.p o) m F s a b
    science :∀ V':Orbit (mid C B),∀ h:IsStarProjection (spar j R.J.M (K V')),∀ p': Wave (Dwell (mid C B)),pilotH P R K V' h (acts (∑ i:Aura (mid C B), F i V') p')= acts (V V') (pilotH P R K V' h p')
variable {O: Seat (mid C B)}{F':Bag (mid C B)}(hF:Nest P R K q l O m s V F' a b)
lemma nestScale (w:ℂ)(hW:Nest P R K q l O m s V F' a b) :Nest P R K q l O m s (w • V) (w • F') (‖w‖*a) (‖w‖*b):=by
 refine ⟨hW.pouch.swell _,fun y h T=>?_⟩; simp only [Pi.smul_apply,←smul_sum]; rw [act_smul,act_smul,map_smul,hW.science]
lemma nestUp (u:a≤c)(v:b≤d)(hW:Nest P R K q l O m s V F' a b) : Nest P R K q l O m s V F' c d:=⟨hW.pouch.bigR u v,hW.science⟩
local notation "Q'"=> scald R.p (Ione.head_L R.F)
include u z
lemma knock (w:R.slip=0)(hs:0 ≤ s)(hd:0 < d)(hz:Fence gR gP K R.p q l O m (s+d+d) V a b) (hp:Sectoral R.p q (scald R.p (Ione.head_L R.F)) m (s+d) c) : let t:=2*(spanV R.p.B*d⁻¹ * a*c); let Z:=t+(2:ℝ)⁻¹*(2*(spanV R.p.B*d⁻¹*t*c));∃ F:Bag (mid C B),Nest P R K q l O m s V F (a+Z) (b+Z):=by
 obtain ⟨J,Q,T⟩:=hz.stock; obtain ⟨F,p,h⟩:= Q.ticket; let U:=tailor R.p R.F F; refine ⟨U,tailor_price R.p p hp hs hd,?_⟩; intro x hx A
 let V':=K x; have ht: JointJ (spar j R.J.M V') (R.J.P.den V') 0 (V x) (giveB F x):=by
    have he:=T x; rw [Moire.bloom_P,h] at he; exact he
 let L:= nursery _ hx; let v₁:= ballL L (relV P R.J V')
 have hv: exponentL R.p R.slip x.1=0:=by rw [w]; simp [exponentL,numbE]
 let G:= exponentL R.p R.F x.1; let y:= Complex.exp (R.betaL K x)
 have hy(p':Wave (Dwell N)):pilotH P R K x hx p'= y • v₁ (acts (exp G).val p'):=by
    change y • v₁ (acts (exp (G+ exponentL R.p R.slip x.1)).val p')=_
    rw [hv,add_zero]
 let Fk:= acts (exp G).val A; have hh: acts (V x) (v₁ Fk)=v₁ (acts (giveB F x) Fk):= ht.sends hx _ (Spire.sea_g z V' (u.paid x) R.J.M) Fk
 rw [hy,hy,map_smul, ←show giveB U x=_ from Finset.sum_apply ..,show giveB U x=_ from tailor_at R.p p hp hs hd x,←act_mul,attireExp _ _ ht.rank,act_mul,hh] -- tune annotation
end YM.CF.Swell
