import ForceSatin.Outpost
import YM.SU5.SatinWard.Resolution.FF
import YM.SU5.SatinWard.Resolution.Aroma
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 4000
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey

open _root_.YM.Gleam.Luster.Risa Gentle Tiling
open BProof (scaleY PL)
open _root_.YM.Work.F03 _root_.YM.Regis
local notation "Uₛ" s:max i:max k:max => gram Y s i k
local notation "Kₛ" s:max k:max => Y.uv k - s
local notation "π₀"=> P.K.top.clip

-- uniform scalar exponents charges
open _root_.YM.Next.Rank.Spindle
open Gentle.Solace Rail
open _root_.YM.Regis.Resonance Lull
open Fineness
namespace Moon
-- genuine Mark polynomial & cost. Keep support and masks explicit; period registration asserted separately
variable {N:Side}{cN:Side}{r:Lattice.Ratio cN (More N)} (T:Tiling cN N r)
variable (S:Support (More N)){H₁:Bed} {Z:PathData SU.group}  {q:Clip} {η CS W t x β y:ℝ}
variable (R:Rules SU.group)(B:Z.Bounds q η CS W) (P₁:Attached H₁ Z)(L:Side)
variable {v' τ:ℝ}(M0:Floor H₁ q (More N) τ v') (O:Bid.Sworn H₁ (More N) SU.group)
open ProbabilityTheory
open Lifted Afterglow Satin Cygnet Loaves Horizons InnerProductSpace
open _root_.YM.Regis.Head
-- tan. build covariant matter pair & color path. actual replica estimators, phase winds paid at both
open FoliageP Lifted Loaves Horizons Afterglow.Tower
namespace Moonlit
-- public builders for the tensor optics. NB use Work.PointB convention. Not the interactive Ward certificate.
namespace SwitchC
namespace Garland
open CF.SU
-- vars
open Tapestry
namespace Terrace
namespace Juniper
-- gauge colour loan.Want arbitrary β-anchor.Core Y calls on operator from G perpetual.Program
open StressFlux AnalyticBridge.VerifiedReset
section Cover
-- pavilion proofs here follow Silk.Span.Rapt & related
def pavilion (X:Cover)(r:ℕ):Finset Cover := (Lattice.box r).image (·+X)
lemma pav_v (X Y:Cover)(r:ℕ): Y∈ pavilion X r ↔ ∀ i:Axis, X i - r ≤ Y i ∧ Y i ≤ X i + r:=by
 constructor
 · rintro p; obtain ⟨v,u,rfl⟩:= mem_image.mp p
   intro i; have ht:=(box_test.mp u).1 i; have hp:=(box_test.mp u).2 i
   change X i- r ≤ v i + X i ∧ v i + X i ≤ X i + r; omega
 intro p; refine mem_image.mpr ⟨Y-X,box_test.mpr ⟨fun i=> ?_,fun i=> ?_⟩,sub_add_cancel ..⟩
 all_goals specialize p i; simp only [Pi.sub_apply]; omega
lemma walk_pav (x y:Cover)(w:Walk)(h:y∈visits x w):y∈ pavilion x w.length:=by
 have he:= Extra.Iteration.along_size x y w h; rw [pav_v]; intro i
 have hp: (y i-x i).natAbs≤ w.length := (single_le_sum (s:=univ) (f:=fun k:Axis=>(y k-x k).natAbs) (fun j _=> Nat.zero_le _) (mem_univ i)).trans he; omega
lemma span_walk (x o u:Cover)(r:ℕ)(w:Walk)(p:x∈ pavilion o r)(t:u∈ visits x w):u ∈ pavilion o (r+w.length):=by rw [pav_v]; intro i; have hp:=(pav_v ..).1 (walk_pav x u w t) i; have ht:=(pav_v ..).1 p i; omega
lemma wrap_pav (N:Side)(X:Cover)(r:ℕ): (pavilion X r).image (wrap N)= halo r {wrap N X}:=by
 ext x; rw [mem_image, halo_spec]; constructor
 · rintro ⟨y,h,rfl⟩; obtain ⟨y,v,rfl⟩:= mem_image.mp h; refine ⟨_,mem_singleton_self _,?_⟩; rw [map_add,separation_comm,separation,add_sub_cancel_right]; exact Work.E01.pdist_wrap_le v
 rintro ⟨y,p,u⟩; rw [mem_singleton.mp p,separation_comm] at u; let z:=wrap N X; let a:= Lattice.lift (x-z)
 have ht(i):-(r:ℤ) ≤ a i ∧ a i ≤ r:=by have hx:(a i).natAbs ≤ r:=(component_le _ i).trans u; omega
 exact ⟨a+X,mem_image_of_mem _ (box_test.mpr ⟨fun i=>(ht i).1,fun i=>(ht i).2⟩), by unfold a; rw [map_add,Lattice.wrap_lift]; exact sub_add_cancel ..⟩
def shade (v:Cover)(G:ℝ):MaskShape:= (G,pavilion v 10)
lemma mergeLamp (t:ℝ)(o:Cover)(V:Pane N): blink N [shade o t] V ↔ pingS t (halo 10 {wrap (More N) o}) V:=by simp_rw [blink, MaskN, Satin.region]; simp only [List.mem_singleton,forall_eq,shade,wrap_pav]
-- follow Bloom.Sun
section
variable {G:Gauge}{n:Side}
variable (F:PlaqAxes)(N:Site n)(V:Config G n)
local notation "Aᴢ"=> F.val.1
local notation "Uᴢ"=> F.val.2
local notation "ν₁"=> negDir Aᴢ
local notation "ν₂"=> negDir Uᴢ
local notation "π₁"=> posDir Aᴢ
local notation "π₂"=> posDir Uᴢ
abbrev meanT {T:Type*}[AddCommMonoid T][Module ℝ T] (f:Fin 4→T):= (4:ℝ)⁻¹ • ∑ i,f i
abbrev nameT : Fin 4→Walk:= ![[],[ν₁],[ν₂],[ν₁,ν₂]]
abbrev springT : Fin 4→RG.Slot:= fun i=>⟨nameT F i,F⟩
lemma plateNext (a b:Step) : G.adjoint (a.read V N) (plate V (N+a.vec) a.rev b) = - plate V N a b:=by rw [plate_rev,map_neg,← G.adjoint_mul, mul_inv_cancel]; simp -- tune
lemma plateWest (a b:Step) : G.adjoint (b.read V N) (plate V (N+b.vec) a b.rev) = - plate V N a b:=by rw [plate_swap V (N+b.vec),map_neg,plateNext,plate_swap V N b a]; simp
lemma toward_face(W:Walk): (RG.Slot.mk W F).atSite V N= G.adjoint (travel V N W) (plate V (stop N W) π₁ π₂) :=by rw [atSite_path, show slotFace ⟨W,F⟩ N=(stop N W,F) from ?_]; rfl; unfold slotFace Slot.offset; rw [wrap_stop_cover,map_zero,add_comm, ← Work.E03.stop_add_left,add_zero] -- tune
lemma mean_petal : petals V N F= meanT (fun i=> (springT F i).atSite V N):=by
 let u i:= (springT F i).atSite V N
 have hg(W:Walk)(i)(h:W=nameT F i): u i= G.adjoint (travel V N W) (plate V (stop N W) π₁ π₂):=by subst W; exact toward_face ..
 have ha := hg [] 0 rfl; have hb:= hg [ν₁] 1 rfl; have hc:= hg [ν₂] 2 rfl; have hd:= hg [ν₁,ν₂] 3 rfl
 have hx: G.adjoint ((ν₁).read V N) (plate V (N+(ν₁).vec) π₁ π₂) = -plate V N ν₁ π₂:= plateNext ..
 have hv: G.adjoint ((ν₂).read V N) (plate V (N+(ν₂).vec) π₁ π₂) = -plate V N π₁ ν₂:= plateWest ..
 have hp: G.adjoint ((ν₂).read V (N+(ν₁).vec)) (plate V (N+(ν₁).vec+(ν₂).vec) π₁ π₂) = -plate V (N+(ν₁).vec) π₁ ν₂:=plateWest ..
 have hw: G.adjoint ((ν₁).read V N) (plate V (N+(ν₁).vec) π₁ ν₂)= - plate V N ν₁ ν₂:=plateNext ..
 simp only [stop,Lattice.travel,G.adjoint_one,mul_one,hx,hv,G.adjoint_mul,hp,map_neg,hw,neg_neg] at ha hb hc hd
 change clover V N Aᴢ Uᴢ=meanT u; unfold meanT clover StressFlux.stencil; congr 1; rw [Fin.sum_univ_four,ha,hb,hc,hd]; abel
end
variable (F G:PlaqAxes) (o:Cover)(x e t:ℝ)(k:Fin 4)
def quadrant (L:Walk): CSocket o:=⟨(stop o L,F),⟨L,rfl⟩⟩
abbrev cornerT : CSocket o:= quadrant F o (nameT F k)
lemma corner_pay (W:Pane N) : cropT N (cornerT F o k) x W=x • (springT F k).atSite W (wrap (More N) o):=by
 rw [springT,toward_face]; unfold cropT cornerT quadrant FaceN arcT Np; simp only [wrap_stop_cover,map_smul]; rfl
-- choose mask thresholds `temp X`, not helpers p.threshold.
local notation "M_"=> (shade o t)
def petalD:ℕ:= 20+colorCash SU.group
lemma length_corner : (nameT F k).length ≤ 2:=by fin_cases k <;> decide +revert -- variable F? decidable reduction with rfl: `decide +revert` might compile finite proofs.
lemma pavLend (o:Cover){y:Cover}{r k:ℕ}(u:r≤k)(t:y∈pavilion o r):y∈pavilion o k:=by rw [pav_v] at *; intro i; specialize t i; omega
lemma pavExpand(o:Cover){T':Finset Cover}{a b:ℕ}(u:T'⊆pavilion o a): Satin.liner T' b ⊆ pavilion o (a+b) :=by
 intro y p; obtain ⟨x,t,P⟩:= mem_biUnion.mp p; apply (pav_v ..).2; intro i; have he:=(pav_v ..).1 (u t) i; have ht:=(pav_v ..).1 (show y∈pavilion x b from P) i; omega
lemma ends_corner : (cornerT F o k).p.1∈pavilion o 2:=by
 let W:= nameT F k; have hp:∀ (W:Walk)(x:Cover), stop x W∈visits x W:=by intro W; induction W <;> simp_all [stop,visits]
 exact pavLend o (length_corner F k) (walk_pav o (stop o W) W (hp W o))
lemma inclPav (o:Cover)(a b:ℕ)(h:a ≤ b): pavilion o a⊆ pavilion o b := by intro i z; exact pavLend o h z
lemma collectPetal (S:Finset Cover)(o:Cover)(a b r:ℕ)(p:a+b ≤ r)(q:S⊆pavilion o a): Satin.liner S b ⊆ pavilion o r:= Finset.Subset.trans (pavExpand o q) (inclPav o _ _ p)
theorem voucherLap (r':ℕ) (u:10+4≤r') (h':2+colorCash SU.group ≤ r') (h:t=Pressure.temp x)(y:2≤Moon.voucher x): UseLens (cornerT F o k) (shade o t) x 1 (pavilion o r'):=by
 subst t; let a:=cornerT F o k; let he:= ends_corner F o k
 have d:Satin.liner (pavilion o 10) 4 ⊆ pavilion o r':= collectPetal (pavilion o 10) o 10 4 r' u (Finset.Subset.refl _)
 constructor
 · exact use_liner _ (S:=pavilion o r') d ((one_mul _).le)
 · exact collectPetal {a.p.1} o 2 (colorCash SU.group) r' h' (singleton_subset_iff.mpr he)
 · unfold shade; change (cornerT F o k).p.1∈pavilion o 10; exact pavLend o (y:=(cornerT F o k).p.1) (r:=2) (k:=10) (show 2≤10 from by norm_num) he
 · exact le_refl _
 constructor
 · intro i p; have v:= length_corner F k; exact pavLend o (show (nameT F k).length ≤r' from (v.trans (show 2≤r' from le_trans (by norm_num) u))) (walk_pav o i (nameT F k) (List.mem_toFinset.mp p))
 change ((nameT F k).length:ℝ) ≤ Moon.voucher x; exact le_trans (by exact_mod_cast length_corner F k) y
lemma voucherAt (h:t=Pressure.temp x)(y:2≤Moon.voucher x): UseLens (cornerT F o k) (shade o t) x 1 (pavilion o petalD):= voucherLap F o x t k _ ((show 10+4≤20 from by decide).trans (Nat.le_add_right 20 (colorCash SU.group))) (Nat.add_le_add_right (show 2≤20 from by decide) (colorCash SU.group)) h y
-- pack square product after pricing, amounts ℂ on EACH term. 
abbrev CupCoin := Fin 4 × Fin 4
abbrev CardDeck := Σ _c:CupCoin,(Σ _i:Sage,Sage×Sage)
noncomputable abbrev hinge (c:CupCoin):=weightT (Terra M_ M_ (cornerT F o c.1) (cornerT G o c.2)) (1/16)
noncomputable def pigment : Tab CardDeck:= packT univ fun c:CupCoin=> hinge F G o t c
lemma monoPig (h:t=Pressure.temp x)(p:2≤Moon.voucher x): SwitchC.ticket (pavilion o petalD) 1 x 2 (pigment F G o t) :=packed_ticket _ _ fun i _=> Tab.weight_ticket (terrify _ _ (voucherAt F o x t i.1 h p) (voucherAt G o x t i.2 h p)) _
lemma pigmentGauge : zeroF (pigment F G o t):=by
 rintro ⟨c,l,i,j⟩ _; rfl
lemma pig_cost {K: Calibration}: Tab.holds K x (pigment F G o t):= pack_holds _ _ fun _ _=> Tab.holds_weight (terra_neutral _ _) _ -- args
abbrev withPaint (o:Site (More N))(t:ℝ)(f:Pane N→ℂ) (V:Pane N):FC (Single N):= (if pingS t (halo 10 {o}) V then f V else 0) • 1
abbrev panel (o:Site (More N)) : Mark N:= fun V=> withPaint o t (fun V=> (x^2*inner ℝ (petals V o F) (petals V o G):ℝ)) V.1
lemma pig_pho (K:Calibration)(m:Side)(U:Fields (K.c m)): (pigment F G o t).cookP x K m U = panel F G x t (Np (K.c m) o) U:=by
 let V:=U.1; let N:=K.c m; let A:= Np N o
 have he(c:CupCoin): checkLen M_ M_ N (cornerT F o c.1) (cornerT G o c.2) x V= if pingS t (halo 10 {A}) V then x^2*inner ℝ ((springT F c.1).atSite V A) ((springT G c.2).atSite V A) else 0:=by simp only [checkLen, mergeLamp,and_self,corner_pay,real_inner_smul_left,real_inner_smul_right,Np, V,A]; rw [pow_two,mul_assoc]
 unfold pigment; rw [packed_stock]; rw [Finset.sum_apply,Finset.sum_apply]; change (∑ i:CupCoin,(hinge F G o t i).cookP x K m U) = _; simp only [hinge,Tab.cook_weight,Pi.smul_apply,terra_pay]; change (∑ i:CupCoin,(1/16:ℂ) • ((checkLen M_ M_ N (cornerT F o i.1) (cornerT G o i.2) x V:ℂ) • _))= withPaint A t _ _
 unfold withPaint; by_cases h: pingS t (halo 10 {A}) V
 · simp_rw [he,if_pos h, smul_smul, ←Finset.sum_smul]; congr 1; simp_rw [mean_petal,meanT,real_inner_smul_left,real_inner_smul_right, sum_inner, inner_sum]; rw [Fintype.sum_prod_type]; push_cast; simp only [Finset.mul_sum] -- tune left constant x². 
   rw [if_pos (show pingS _ _ U.1 from h)]; dsimp only [V,A,N]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
 simp_rw [he,if_neg h]; rw [if_neg (show ¬pingS _ _ U.1 from h)]; simp
abbrev wage:ℝ:= ∑ _i:CupCoin, (1/16:ℝ)*((Fintype.card Sage:ℝ)*((Fintype.card Sage:ℝ)*Fintype.card Sage))
lemma costPigment : (pigment F G o t).terms=wage:=by unfold pigment wage; rw [packed_price]; simp only [hinge,Tab.weight_cost,price_ter]; norm_num
end Cover
end Juniper
end Terrace
end Garland
end SwitchC
end Moonlit
end Moon
end Papal
end LocalLimit
end Rate
end YM.CF.Py
