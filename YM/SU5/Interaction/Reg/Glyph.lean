import YM.SU5.Interaction.Reg.High
import YM.CF.Vp929.Match.Rays

/-! (124), the three Glyph.fondC budgets in the real branch. Need the actual vote functions, not recomputation by the high exponent. Use same écu. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
namespace Glyph
variable {δ a b u e W:ℝ}{μ:Toll (Single n)}{S:Support (More n)}
variable (F:Raw (Openc (More n) δ) (Single n)){q:ℕ}{K:Scree.Loom n}(p:Roof n a δ q K)(g:0<δ)(t: Suite (badge _) (bail n δ) (bail n δ) S μ F)
variable {H:Op (Single n)→FC (Dwell n)}{Z':Single n→ Single n→ FC (Dwell n)}{h:ℝ}(f: Glyph H Z' h)
variable (T:Scree.Hub n)(z:T.val.1∈ S)(x:S∈αW P.B (Bake.lagE T))
open Ione Bake Nor Larch Levier Salt
local notation "Hz"=>Scree.Hub n
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
variable (w:Sweep n)(M:Elm n κ δ e u)
local notation "R"=> Salt.actY w
local notation "W'"=> moveHub w
local notation "GZ"=> panel P
local notation "Λ"=> Ione.suit_Y w
local notation "Δ"=> sauce w.charge (detX w.s) (Sour.γS w)
variable (i:κ)
variable {e' a' b' :ℝ}(v:P.threshold ≤ a)(bq:q+10 ≤ P.B)(hk:cipherK q ≤ 5*P.B)(uB:3≤P.B)(p0:HopeT δ e' a' P.order)(t0:P.threshold ≤ a')(h0:1≤h)

local notation "Xq"=> fondC p g M H P i
include p g f v bq hk uB p0 t0 h0
lemma glyphBudget (y:ℝ)(h₀:∀ o:Seat n,(∑ T:Scree.Hub n, if T.val.1=o then ((ups P).mass T.val.2 (@écu _ (ups P) h M.W T)) else 0) ≤ y): IncX (fun _=>False) Xq (ups P) h y := by
 refine ⟨⟨fun j => @écu _ P h M.W j,fun j=>upsPress (essay p g f j M i v bq hk uB p0 t0 h0),?_⟩,fun _ t=>t.elim⟩
 intro o; simp_rw [eq_comm (a:=o)]
 exact h₀ o -- écu defeq even though its parameter is not ours. 
end Glyph
end YM.CF.Sour
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
variable {N:Side} (T S:BeatL N)(E:χL N κ)
local notation "Sta"=> fC N S E
local notation "Bel"=> κR N E
local notation "Q"=> tickA N
local notation "Lx"=> Firing N
namespace BondL
variable {a b c d e s:ℝ}{T S E}(A: BondL T S E b c a d){p:BudgetPoint}{L:Scree.Loom N}{q:ℕ}{t:ℝ}(g:Roof N t d q L)(h:0<d)(W:ℝ)(w0:1 ≤ W)
variable (s_:Sweep N)(V:Orbit N)(i:κ)(Z:Aura N)(pF:Injective (priorP V.2))
open Levier Salt Ione
local notation "Λ"=> sauce s_.charge (detX s_.s) (γS s_)
local notation "OA"=> σX p Z ∅
local notation "WZ"=> yellA s_ V
local notation "Px"=> p.B
local notation "Sg"=> Support (More N)
local notation "Ut"=> (moldA s_ Z)
open Cadre Wray Larch Ione
variable {H p0:ℝ}{I: Aura N→ Support (More N)→ ℝ}(F:Vow.Cusp N)
variable {z0 z1:ℝ}(k: HopeT d z0 z1 p.order)(hv:p.threshold ≤ z1)(y:p.threshold ≤ t)(hx:q+10 ≤ p.B)(v:cipherK q ≤5*p.B)(w:3≤p.B)
variable (f:∀ X:Aura N,∀ D⊆X.val,Fray p W (cipherK q) X D (F X D) (I X D))(r:Bake.Turf (fun X=>F X ∅))
variable (pS: ∀ s:Sweep N,∀ i:Aura N,∀ V:Orbit N,Injective (priorP V.2)→∀ D⊆i.val,F (moldA s i) (actY s D) (yellA s V)=suit_Y s (F i D V))
local notation "τx"=> A.bead W p
local notation "L'"=> (fun i:κ=> litB A g h W w0 k hv y hx v w i)
open Stax Glyph
local notation "Θi"=> (L' i)
local notation "B'"=> Λ
local notation "K'"=> Bias.payX Θi
local notation "φS"=> fun A:Op (Single N)=> Matrix.trace A • (1:FC (Dwell N))
variable {κ':ℝ}(uA:Sour.pureB A κ') (T0:Finset (Scree.Hub N))(Y0:∀ T:Scree.Hub N,coverNumber p.B T.val.2 ≤ 1→T∈T0)
local notation "μs"=> A.lineH (p:=p) g h i
local notation "Yb"=> A.floatH (p:=p) g h i
local notation "Kα"=> A.scarf (p:=p) g h i
local notation "Ωa"=> A.seekB (p:=p) g h i
include w0 k hv y hx v w
variable (he:0 < a)(fα:2*(ups p).supportExponent*Fief.tileN 1 ≤ a/2*p.B)(e': a ≤1)
include uA he fα
lemma starHigh : IncX (fun _=>False) μs (ups p) W (cap1 (ups p) (øK κ') W):=
 glyphBudget g h (pal_v W w0) A.ela i y hx v w k hv w0 _ (payWorth A.ela uA.1 fα he uA.2)
omit uA
include e'
lemma payFloatHigh : IncX (fun _=>False) Yb (ups p) W (cap2 (ups p) c W a):=
 glyphBudget g h (pal_v W w0) A.elt i y hx v w k hv w0 _ (payW A.elt A.elt.bank fα he e')
lemma payScarfHigh : IncX (fun _=>False) Kα (ups p) W (cap2 (ups p) b 1 a) := by
 have ht:IncX (fun _=>False) Kα (ups p) 1 (cap2 (ups p) b 1 a):=
    glyphBudget g h (oreV 1 le_rfl _) A.coreS i y hx v w k hv le_rfl _ (payW A.coreS A.coreS.bank fα he e')
 obtain ⟨x,K⟩:=ht; obtain ⟨v₁,f,v'⟩:=x; exact ⟨⟨v₁,fun X=> pose_k X _ W (f X) (Glyph.dust g h X A.coreS i y hx v w k hv), v'⟩,K⟩
end BondL
end YM.CF.Sour
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}{a b c d C r:ℝ}[Nonempty (Haro.ΘS r)]
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial Haro
namespace MatchW
open Py.Rate Haro Cadre Wray Larch Ione
open Push.AbsoluteSums Haro Glyph Trees
open scoped Mew
local notation "Qu"=> Tenant.quota^2
variable (T S:BeatL n) {p:BudgetPoint}{v W e:ℝ}{B:ℕ}{L:Scree.Loom n}
open Technique
variable {T S} (Ω:Technique p W e d B L T S a b c r)
namespace Technique
local notation "Xp"=> Ω.note + Ω.note
local notation "Kr"=> Rinse (Seat n) (Copy n)
local notation "Er"=> ΘS r
local notation "λχ" i:max=> Ω.bond.litB Ω.H Ω.pay W Ω.floor Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize i
local notation "πχ"=> Pair (ΘS r)
local notation "I_"=> Complex.I
variable {Wk f m₁ m₂ u0 Λ ψ δ θ x g γΓ θΓ dΓ vδ r₁ s:ℝ}
local notation "Pk"=> cap1 p (BondL.øK r) W
local notation "VK"=> Vow.Cusp n
local notation "Θp"=> Py.Mood p (512*Wk) W a (Tenant.quota^2 * b) (Tenant.quota^2 * c) r s m₁ m₂ u0 vδ r₁ Λ ψ θ δ γΓ θΓ dΓ
variable (Th: Py.Mood p (512*Wk) W a (Tenant.quota^2 * b) (Tenant.quota^2 * c) r s m₁ m₂ u0 vδ r₁ Λ ψ θ δ γΓ θΓ dΓ)
local notation "opV" I:max k:max=> Timer (Cadre.chip (cribR (Ω.note+Ω.note)) I) (Ω.note+Ω.note) r₁ (wu p) wΨ (widthK n p.B) (spanV p.B) γΓ dΓ (spanV p.B*dΓ) dΓ k (Ω.note+Ω.note)
local notation "gΨ"=> degreePrice p.B θΓ wΨ
local notation "Upp"=> uk_b (rentΦ p γΓ dΓ) vδ θΓ gΨ
local notation "αΒ"=> p.supportExponent+1+1
include Ω Th
lemma rollHigh (i:Er):IncX (fun _=>False) (Ω.lerW i) (ups p) W (φcape (ups p) a (Qu*b*r) (Qu*c*r) W)∧ IncX (fun _=>False) (Ω.ler i) (ups p) W (cap1 (ups p) (BondL.øK r) W):=by
 rw [mul_assoc Qu b _,mul_assoc Qu c _]; let A:= Ω.bond; let k:= (show 2*(ups p).supportExponent * Fief.tileN 1≤ a/2*p.B from ?_); exact ⟨Larch.add_v (ups p) _ _ (A.payFloatHigh Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.pos k Ω.raw) (A.payScarfHigh Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.pos k Ω.raw), A.starHigh Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.economic Ω.pos k⟩
 have ht:=Th.speed.nf
 change 2*(p.supportExponent+1)*(Fief.tileN 1) ≤ a/2*p.B
 apply le_trans _ (ht.trans ?_)
 · refine mul_le_mul_of_nonneg_right (by unfold wu; linarith) (by positivity)
 apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
 linarith only [Ω.pos]
end Technique
end MatchW
end YM.CF.Sour
