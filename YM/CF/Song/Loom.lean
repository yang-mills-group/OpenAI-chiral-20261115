import YM.CF.Song.Past
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Sour Haro Tap Ione Larch Nor Glyph SupportP
variable (P_:BudgetPoint)(H:ℝ)
local notation "Qb"=> QuotaH V.f V.g V.F1 V.F2
local notation "pα"=> arcB V.f V.g V.F1 V.F2
open Cube
abbrev tatE :WG (QuotaH V.f V.g V.F1 V.F2):=fun i=>funde K.j i.2
abbrev tagE :WG (QuotaH V.f V.g V.F1 V.F2):=fun i n x=> Kennel.capT (tatE V i n x) (arcB V.f V.g V.F1 V.F2 i n x)
variable (htK:1≤K.j)
include htK
lemma tass : Lively (tatE V):= boost _ (funde_s K.j htK) Prod.snd
lemma φ_live : Lively (tagE V) ∧∀ i:Qb,∀ n:Side,tagE V i n 1=0:=by
 obtain ⟨a,h⟩:=alum V.pos1.le V.pos2.le V.width1 V.width2
 exact ⟨((Lively.one.sub (tass V htK)).prod a).prod (tass V htK),fun i n=>by unfold tagE Kennel.capT; rw [h,mul_zero,zero_mul]⟩ -- cap order inspect
structure MotD(a b c M:ℝ)(j:ℕ):Prop where
 fresh: η₁ ≤ b
 earn (i:QuotaH V.f V.g V.F1 V.F2)(N:Side)(t:ℝ)(e:ℝ): 0<t → j ≤ N.val→0 < e→ e ≤ M→Sour.Piety N (tatE V i N) (tagE V i N) (Sour.body_Q (N:=N) t) a t (b*t) (c*t) e
lemma ores (p:0 < H): ∃ e a b c :ℝ,0<e∧ 0<a∧a ≤1 ∧(∀ᶠ W:ℝ in atTop,lobe H W (γ₀ P_ a (Tenant.quota^2*b) (Tenant.quota^2*c) 0 W) P_)∧∃ j:ℕ,MotD V a b c e j:=by
 obtain ⟨ε,hq,z⟩:=era_x P_ H p; let k:=numV P_+1; obtain ⟨f,s⟩:= φ_live V htK; obtain ⟨a,b,c,M,x,y,t,Z,pM,v,j,hv⟩:= Sour.mood _ _ (tass V htK) f s k ε hq -- type index
 let b':=max b η₁; have hk:a/(k+1:ℝ)≤a:=div_le_self x.le (by simp)
 refine ⟨M,a,b',c,pM,x,v,z x t (le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : 0≤ a⁻¹) (inv_anti₀ (by positivity) hk) k) t) Z),j,le_max_right ..,fun i N t e hp he k w=>?_⟩
 let z00:ΘS t:=⟨0,by rw [norm_zero]; exact hp.le⟩; haveI : Nonempty (ΘS t):=⟨z00⟩; have hQ:=hv N he i t e k w hp.le (ΘS t) (body_Q (N:=N) t) (continuous_subtype_val.comp continuous_subtype_val) (fun i=>i.val.property) (fun i=>i.property); have ht:b*t≤ b'*t:=mul_le_mul_of_nonneg_right (le_max_left ..) hp.le
 exact ⟨hQ.kX.tall ht,hQ.bend,hQ.loan.tall ht,hQ.pX.tall ht,hQ.pY.tall ht,hQ.pZ.tall ht⟩
open Thera
variable {D:Side} {t pK :ℝ}(U:Grasp V.U B d)(T:GivenX V U)(Y: GramM (mid D B))(u:Hom.InterestX T.C (mid D B) Y.J)(hX:U.roundZ ≤ (mid D B).val)
include u hX
lemma rise_F (D':Qb)(r':ℝ)(hY:(D'.1 (mid D B)).val=Y.J.P)(g':D'.2=Y.J.M)(w:e ≤ d): TagT (tatE V D' (mid D B)) (tagE V D' (mid D B)) (body_Q (N:=mid D B) r') e:=by
 intro i p; have t:= u.leanJ.1; have hc:=u.ready; let N:= (mid D B); let T:=tatE V D' N; let S:=tagE V D' N; have ht(i):T (Tulip.profile i)= spar K.j Y.J.M i:=by unfold T tatE; rw [g']; rfl
 have hg:=U.broadness _ hX Y.J.M; have hv:= (p.shrink w); have hV(i)(p:Guard i d):IsStarProjection (T (Tulip.profile i)):= by rw [ht]; exact hg.projection i p
 refine ⟨hV _ hv,fun s=>?_⟩; let a:=castX s; let b:=s.charge; let M:=spinU b s.s; let v:=detX s.s; let X₀:=T (Tulip.profile i); let Wκ:= flashA s i; let X₁:=T (Tulip.profile Wκ); let K':= siteU a b M N; have he:JetS a.s b v M:=spinZ ..
 have hx:sings b K' X₀=swapX v X₁:=by
    change sings b (prepU a M (xtra b) N) (funde K.j _ _ (Tulip.profile i))=_; exact funde_f _ _ _ he _ _ htK _ _ (V.note.fields_one _ (U.needed.trans hX)) (hv.shrink U.gem)
 have ht':= hV Wκ (keepC (xtra b) a i d hv); have h(u):pα D' N (Tulip.profile u)=Y.J.P.den u:=by unfold arcB; change Moire.bloom (D'.1 (mid D B)).val _= _; rw [hY,Moire.bloom_P]; -- tune
 refine ⟨?_,?_,fun i=> i.val.property⟩; · change X₁=swapX v (sings b K' X₀); rw [hx]; cases v <;> simp [swapX]
 change Kennel.capT X₁ (pα D' N (Tulip.profile Wκ))= Thera.jazz v (sings b K' (Kennel.capT X₀ (pα D' N (Tulip.profile i))))
 have hq:pα D' N (Tulip.profile Wκ)= Thera.jazz v (sings b K' (pα D' N (Tulip.profile i))):= by
    unfold N arcB; rw [hY]; exact Levier.prism_x b a Y.J.P t hc i M he
 rw [hq]; exact Levier.prima _ _ _ _ ht' hx -- tune
omit htK
lemma dusk(V:Pane (mid D B))(p:Guard V e)(w:e≤d):IsStarProjection (spar K.j Y.J.M V):= (U.broadness _ hX Y.J.M).projection _ (p.shrink w)
omit u hX
end YM.CF.Py
