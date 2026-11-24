import YM.SU5.FiniteGaugeData.Brique.Crater
import YM.CF.Hive.Hen
/-! The reflecting Peg test is sound on every actual trajectory (Buy enough room for S.toll, uniform shelves later).
    True determinant mark, no phase pricing at all in these estimates apart from where absolute Treasury is charged.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Window.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Spire Tenant Buffered Fock Fock.Brique Tulip Dial Skye Scree Cascade Hom Vale Nacre Paige Vault
attribute [local instance] opCStarAlgebra
variable {m B N L:Side}{k:ℕ}{o:Odd L.val} {Y: Pricing k L o (Thread k)}{I:Interest N}{e:ℝ}(D:Grasp Y B e)
-- b'=domination constant; true orientation
abbrev shift₁(k:ℕ)(Z:Interest N)(U:Pane N): Op (Single N):= Kennel.capT (spar k Z.M U) (Z.P.den U)
abbrev blend (k:ℕ)(Z:Interest N)(b:Bool)(U:Pane N) := if b then 1-spar k Z.M U-star (shift₁ k Z U) else spar k Z.M U+shift₁ k Z U
-- rib license (strongly matched at THIS male and field)
structure Bracewell (k:ℕ)(Z:Interest N)(e:ℝ): Prop where
 pin(P:Pane N): Guard P e → IsStarProjection (spar k Z.M P)
 side (a:Axis)(z:ℤ)(b:Bool)(y:Pane N): Guard y e →blend k Z (!b) (fling a z N y)= twist (carR a z N) (blend k Z b y)
variable {a b c C:ℝ}{Z:Interest N}
lemma bracewell {D:Grasp Y B e}(h: D.roundZ ≤ N.val)(w:Stamped k L o Y)(t: 1 ≤ k)(p:Z.P.toll a b c C): Bracewell k Z e:= by
 let V:= D.broadness N h Z.M; refine ⟨fun P g=>V.projection P g,?_⟩
 intro i z b x q; let S:=Buffered.plane i z; let U:=carR i z N; let W:= fling i z N x
 let X:= spar k Z.M x; let T:= spar k Z.M W
 have hv: Guard W e := keepC inert S x e q; have he: twist U X=1-T:= funde_f S inert (pinLift i) (mirrorX i) x k t Z.M Y.e (w.fields_one _ (D.needed.trans h)) (q.shrink D.gem)
 have hx:Z.P.den W = -(star (twist U (Z.P.den x))):=by
    have hS: detX S.s=true:= det_t i; have R: JetS S.s false (detX S.s) (pinLift i):= hS ▸ mirrorX i -- tune
    have he:= (Levier.dawn S _ p x).trans (z_spin _ _ _ R); rw [hS] at he; exact he
 have h₁: shift₁ k Z W= - star (twist U (shift₁ k Z x)):=by
    have hz:= Levier.prima (b:=false) (r:=true) U X T (Z.P.den x) (V.projection _ hv) he; unfold shift₁; rw [hx]; exact hz
 unfold blend; cases b; · change 1-T- star (shift₁ _ _ W)= twist U (X+_); rw [map_add,h₁,star_neg,star_star,he]; abel
 change T+ _ = twist U (1-X- star _); rw [h₁,map_sub,map_sub,map_one,map_star,he]; abel
-- Peg buys aperture fixed D. actual seats valid.
def Bracewell.peg (p:Bracewell k Z e) : Window.Brique.Peg N:=⟨e,blend k Z,p.side⟩
local notation "Μ" => Single N
-- lens purchases. Note blend_norm below independent score on Z.P shift; actual aperture from elected. 
structure Life (k:ℕ)(Z:Interest N)(e b:ℝ)(u:ℕ)(δ:ℝ): Prop where
 bleed : Bracewell k Z e
 earn : ∀ (y:Pane N), Guard y e → ‖blend k Z false y‖≤ b
 approx : ∀ y:Pane N, Guard y e → ∃ A:Op (Single N), Neighbor u A ∧ ‖A-blend k Z false y‖ ≤ δ
lemma blend_motto (x:Pane N)(h:IsStarProjection (spar k Z.M x)): (1+shift₁ k Z x)*spar k Z.M x= blend k Z false x:=by
 let P:=spar k Z.M x; change (1+ (1-P)*_*P)*P=P+_; rw [add_mul,one_mul,mul_assoc _ P P,(show P*P=P from h.1)]; rfl
variable {r H ε α c₁ c₂ :ℝ}{u j:ℕ}{w:Scree.GramM N}{W:Scree.Loom N}{F:Mark N}
open Graph
lemma boundStaff (x: Pane N)(h:IsStarProjection (spar k Z.M x)) {T:Op (Single N)}(p:IsStarProjection T)(t: ‖T*blend k Z false x‖ ≤ Real.exp (-α))(v:‖blend k Z false x‖ ≤ b): ‖scaleUp T α*(1+shift₁ k Z x)*spar k Z.M x‖ ≤ 1+b:=by
 let A:= blend k Z false x; rw [mul_assoc, blend_motto x h]; unfold scaleUp; rw [add_mul,Algebra.smul_mul_assoc]; apply (norm_add_le ..).trans; refine add_le_add ?_ ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (p.one_sub.norm_le _)).trans v)); rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; exact (mul_le_mul_of_nonneg_left t (Real.exp_pos _).le).trans_eq (by rw [←Real.exp_add]; simp)
variable {w₀:GramM (mid m B)} {F₀:Mark (mid m B)} {W₀:Scree.Loom (mid m B)} {n:ℕ} {S: Support (More (mid m B))}
set_option quotPrecheck false
/-- CAR contribution, normalized Relative & absolute extensive costs in ancestors. -/
theorem cashout (R:Life k w₀.J e b u C)(Q: Crater u C ε R.bleed.peg S F₀ n false)(J:Graph.Ledger H c₁ c₂ r c w₀)(a:0≤ α)(h0:0 ≤ b)(kH:Real.exp α+1 ≤ H)(r': D.roundZ ≤ (mid m B).val)(k:0 ≤ r) (hp:0 ≤ c)(he: ε+C ≤ Real.exp (-α)) (x:Orbit (mid m B))(t:Guard (W₀ x) e): -- k shadows!
 ‖inner ℂ (mateK _) (acts (F₀ (x.1,W₀ x)) (Graph.beam w₀ D W₀ x))‖ ≤ (Real.exp (-α))^n * ‖F₀ (x.1,W₀ x)‖ * (Real.exp (flagBill (mid m B) c₁ c₂ c)*(1+b)^(Fintype.card (Single (mid m B)))):=by
 let y:Fields _:= (x.1,W₀ x); let L:= F₀ y; by_cases H:L=0; · rw [show F₀ (x.1,W₀ x)=0 from H]; simp
 obtain ⟨A,j,hA,eA,zA⟩:= Q.out y t H (R.approx _ t); let Y₀:=changeM D (W₀ x) w₀.J.M; let x':= Graph.beam w₀ D W₀ x; let q:= R.bleed.pin _ t; let G:= mateK (mid m B)
 let Y':= boundStaff (Z:=w₀.J) _ q j (zA.trans he) (R.earn _ t)
 have h: ‖acts (quant (scaleUp A α)) x'‖ ≤ _:= armed J _ _ x q a kH A j k hp (by linarith) Y₀ (sea_g r' _ t _) Y' -- tune
 change ‖inner ℂ G (acts L x')‖ ≤ Real.exp (-α)^n * ‖L‖*_; rw [←act_inner, Full.damped j eA n hA α x',mul_assoc]; refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm ..).trans (mul_le_mul ?_ h (norm_nonneg _) (norm_nonneg _))) (by positivity); exact (wing_opy (star L) G).trans_eq (by rw [norm_star,show ‖G‖=1 from (tickB _).2,mul_one]) -- tune α rewrite mul_assoc may left
end YM.CF.Window.Brique
