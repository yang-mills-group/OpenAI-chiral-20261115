import YM.SU5.SatinWard.Resolution.LatticeFieldEstimates
import SatinThinExpense
import Anomaly.Rack.Ink

-- Register venue of economy for any number of host roots. Keep mark+spawn clearance for one-step purchases.
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 85000
noncomputable section
set_option linter.unusedSectionVars false
set_option quotPrecheck false
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell Porticus QuadClock Ione.Clock Moto Neon Taxi Lor
open Oise Buffered
open Pitching Focus QuadClock.ShapeLab
open Oise Buffered
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (Γ:ℝ)(Pay kc:ℝ)(Tξ:Hove.Grant P.K.j 2)(nmc m:ℕ) (Z V K W:ℝ→ℝ)
variable (uZ:BladeQ P.R Z W V K)(proofW:∀ᶠ s:ℕ in atTop,∀ᶠ i in atTop,∀ k,s<Y.uv k → stockedTap Y Pay kc Γ Tξ nmc m Z V K W s i k)(flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
variable {η ι:Type}[Fintype ι][DecidableEq ι][Fintype η](F:ResolutionFrame ι)(C H A u:ℝ)


open Pail.Dew Swell.Porticus QuadClock.ShapeLab.ResolutionFrame
open Lampshade SignSlot Waxy Tap
set_option linter.flexible false
variable {a b c d U ε f r ψ:ℝ}{s i k:ℕ}
local notation "Bα"=> RootBook Y i k s
local notation "pβ" => (Bα).p
local notation "Λ" => P.Ctor (Y.ir i) s
local notation "V₀"=> (Y.voyage i).CapeT s
local notation "θ"=>lapQ Y s
local notation "ωs"=> hat P.R.L P.x s
local notation "ARE"=>stockRate (Bα).p
local notation "L★"=> P.R.L


open Hove Yoke Buffered Afterglow Journey ShapeLab.ResolutionFrame
namespace Tabletop
-- generic using mint-Schedules: Lex avoids order on mode Λ. Could use direct pair.I.Class.Attaching every mode to every host. 
variable {κ I J:Type}[Fintype κ][LinearOrder I][Fintype I]{N:Side}
abbrev Booth (I κ:Type)[Fintype κ] := Lex (I× Fin (Fintype.card κ))
abbrev desk (x:Booth I κ):I:= (ofLex x).1
abbrev subject (x:Booth I κ):κ:= (Fintype.equivFin κ).symm (ofLex x).2
abbrev bookIn (i:I)(j:κ): Booth I κ:= toLex (i,Fintype.equivFin κ j)
abbrev checkup (i:I):κ↪ Booth I κ := ⟨bookIn i,fun _ _ p=> (Fintype.equivFin _).injective (congrArg (Prod.snd ∘ ofLex) p)⟩
abbrev chassis (κ:Type)[Fintype κ] (o:I→Site N) :=fun i:Booth I κ=> o (desk i)
attribute [-instance] instDecidableEqLex
local notation "WK"=> Booth I κ
variable {r:ℕ}{o:I→ Site (P.Ctor (Y.ir i) s)}
local notation "ηG"=> Cube.node ∘ chassis κ o
local notation "Zg"=> Cube.node ∘ o
local notation "Ω"=> RootBook Y i k s
-- ψS = list of distinct hosts.
abbrev distinctHost (l:List (Booth I κ)):Prop:=(l.map desk).Nodup
abbrev heatLot (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(s i k:ℕ)(o:I→ Site (P.Ctor (Y.ir i) s)) := Very_Ψ o (RootBook Y i k s).p.B
lemma who (x:WK): x=bookIn (desk x) (subject x):=by unfold bookIn subject; rw [Equiv.apply_symm_apply]; rfl -- tune
lemma boom_book (x:I)(y:κ): subject (bookIn x y)=y:=(Fintype.equivFin κ).symm_apply_apply _
lemma surject_subject [Nonempty I] : Surjective (subject (I:=I) (κ:=κ)):= fun x=> ⟨bookIn (Classical.arbitrary I) x, boom_book ..⟩
lemma layout_seats{a:I→Site N}(ε:Injective (Cube.node ∘ a)) : Seating (chassis κ a) subject:=by
 constructor; intro i; let σ:= chassis κ a; let tz:= Cube.node∘a; constructor
 · rintro ⟨x,x'⟩ ⟨y,y'⟩ e; apply Subtype.ext; dsimp only; have H:desk x=desk i:= ε ((mem_filter.mp x').2); have H':desk y=desk i:= ε ((mem_filter.mp y').2); exact (who x).trans ((congrArg₂ bookIn (H.trans H'.symm) e).trans (who y).symm)
 intro q; refine ⟨⟨bookIn (desk i) q,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩,boom_book ..⟩
lemma granule {a:I→Site N}(ε:Injective (Cube.node ∘ a)) (l:List (Booth I κ)) : ψS (Cube.node∘chassis κ a) l ↔ distinctHost l := by
 unfold ψS distinctHost; rw [show l.map (Cube.node∘chassis κ a)=(l.map desk).map (Cube.node∘a) from by rw [List.map_map]; rfl]; exact ⟨List.Nodup.of_map _,List.Nodup.map ε⟩ -- syntax
variable (n:ℕ)(p:Fintype.card κ ≤ n)(v:heatLot Y s i k o)
include p v
lemma lots_force :Force_M ((Ω).p.B) (Cube.node ∘ chassis κ o) n:=by
 let S :=chassis κ o; let X:= (Ω).p.B; have t:=v.1
 have he: Seating (chassis κ o) subject:=layout_seats v.1
 constructor
 · exact fun j k x=> v.2 _ _ x
 intro y; let A:=reach_B (cape_B X) X (Cube.node∘S) y; change A.card≤ _; by_cases g:A.Nonempty; swap; · rw [not_nonempty_iff_eq_empty.mp g]; simp
 obtain ⟨j,w⟩:=g; let U:= pipe_ζ (Cube.node∘S) j
 refine (card_le_card (?_: A⊆ U)).trans (?_: U.card ≤n)
 · intro k h; have hx(i)(g:i∈A): separation y ((Cube.node∘o) (desk i))≤ X+cape_B X:= (mem_filter.mp g).2; refine mem_filter.mpr ⟨mem_univ _,?_⟩; by_contra h'; have e₂ := v.2 (desk k) (desk j) h'; have hz:separation ((Cube.node∘o) (desk k)) ((Cube.node∘o) (desk j)) ≤ X+cape_B X+(X+cape_B X):=(separation_triangle _ y _).trans (add_le_add ((separation_comm ..).le.trans (hx k h)) (hx j w)); change cape_B X+cape_B X+X+X < _ at e₂; omega
 exact (Eq.le ((Fintype.card_coe U).symm.trans (Fintype.card_congr (seat he j)))).trans p
abbrev ticket_B (L:Side)(B:ℕ):= (L.val+1)*(4*B+2)+2*B
local notation "LΛ"=> P.R.L
lemma lotsGap (u:ticket_B P.R.L (Ω).p.B ≤ (Ω).p.B+cape_B ((Ω).p.B)) : GapN (chassis κ o) (Ω).p.B (LΛ).val n:= by
 intro y; exact le_trans (Finset.card_le_card fun i z=> mem_filter.mpr ⟨mem_univ _, ((separation_comm ..).le.trans ((mem_filter.mp z).2.trans u))⟩) ((lots_force Y n p v).2 y)
omit p v
abbrev ApexCall (b:ℕ):=cape_B b+cape_B b+b+b
def boardC (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(s i k:ℕ) :Prop:= let b:=(RootBook Y i k s).p.B; ticket_B P.R.L b≤ b+cape_B b ∧ 2*candleRadius b+4*Levy P ℓ ≤ ApexCall b
lemma rentsHeight :∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s<Y.uv k → boardC Y s i k:=by
 let L:=P.R.L
 have hb:Tendsto (fun i=> (Y.meter.a i).B) atTop atTop:=waist Y 0
 let A:=4*Levy P ℓ+50*L.val+100; filter_upwards [hb.eventually_ge_atTop A] with s t i k v
 have ht:(Y.meter.a s).B=(RootBook Y i k s).p.B:=congrArg BudgetPoint.B (((Y.voyage i).X (Y.uv k)).pull.owns s v.le).width; let b:= (RootBook Y i k s).p.B
 have hx:A≤ b:= t.trans_eq ht; unfold A at hx; have u:L.val+1 ≤ b:=(by omega)
 have h₀: 100 ≤ b:=by omega
 let hp:= show 100*b^2 ≤ b^3 from by rw [pow_succ' b 2]; exact Nat.mul_le_mul_right _ h₀
 change (L.val+1)*(4*b+2)+2*b ≤ b+b^3 ∧ 2*(24*b+12)+4*Levy P ℓ ≤ b^3+b^3+b+b; constructor; nlinarith only [hp, h₀,Nat.mul_le_mul_right (4*b+2) u]; nlinarith
local notation "Rf"=> candleRadius (Ω).p.B
lemma lease_distance (h:boardC Y s i k)(v:Very_Ψ o (RootBook Y i k s).p.B) : Beyond P ℓ o (candleRadius (Ω).p.B):=by intro i y w; exact lt_of_le_of_lt h.2 (v.2 _ _ (v.1.ne w))
lemma beyond_pair {a:I→Site N}(p:Beyond P ℓ a r) (x:List (Booth I κ))(h:distinctHost x): x.Pairwise fun i j=>Disjoint (offsetMask r (chassis κ a i)) (offsetMask r (chassis κ a j)) :=by refine (List.pairwise_map.mp (show (x.map desk).Pairwise _ from h)).imp (fun i=> Contact.spacing 0 _ _ _ _ (lt_of_le_of_lt (show r+r ≤2*r+4*Levy P ℓ from by omega) (p _ _ i))) -- ABI fix
local notation "step★"=> heel (Vale.apt (Y.ir i) P.block P.R.L s)
lemma upperCeiling (z:s<Y.uv k) : candleRadius (RootBook Y i k (s+1)).p.B ≤ grantRadius P ℓ Rf:=by
 let X:=RootBook Y i k s; let V:=RootBook Y i k (s+1); have he: V.p.B ≤2* X.p.B:=by
    let J:= (Y.voyage i).X (Y.uv k); rw [show V.p=Y.meter.a (s+1) from (J.pull.owns _ z).width.symm,show X.p=Y.meter.a s from (J.pull.owns _ z.le).width.symm,(Y.meter.boot s).2.1]; exact (Y.meter.roll s).hU
 unfold grantRadius; have hx:2≤ P.R.L.val:= Nat.le_trans (by norm_num :2 ≤ 3) P.R.coarse; let Q:=grossAt P ℓ; change candleRadius V.p.B ≤_; calc
    _ ≤ 2*candleRadius X.p.B:=by unfold candleRadius; omega
    _ ≤ _ := Nat.mul_le_mul hx (Nat.le_add_right ..)
lemma lotsNext (v:heatLot Y s i k o)(u:s<Y.uv k)(e:10 ≤ P.R.L.val): heatLot Y (s+1) i k (step★ ∘ o):= sprint_B Y i k s u e o v
end Tabletop
end YM.CF.Py.Rate.LocalLimit.Preparation
