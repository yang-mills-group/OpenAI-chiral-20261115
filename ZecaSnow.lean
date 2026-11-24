import YM.SU5.Diva.Jewel
import ZecaMosaic
import YM.SU5.Diva.Tailor
import YM.SU5.Lamour.Matinee
set_option autoImplicit false
set_option maxHeartbeats 320000
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
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open Lamour.Bridge CF.Pannier.Chancel
variable {Z θ b v t ε R C ξ:ℝ} {n a y z' k:ℕ}
universe u0
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
open YM.CF.Lamour.Bridge.Celeste
open YM.CF.Lamour.Bridge.Celeste.Morn
open YM.CF.Lamour.Bridge YM.CF.Velvet
open YM.CF.Lamour
open Sonnet
variable {F F':Weaver} -- fix
variable {N:Side}{d r j:ℕ} {A:Finset Cover} {D E:ℝ}
open Tower.SlabMark
set_option maxHeartbeats 800000
set_option maxRecDepth 8000

/-! # Feather slab estimate, label criteria. -/
variable {p:ℕ}{σ:ℝ}{M:Tulip.Male}
namespace Frost
def frostD (R r p:ℕ):=R+r+p+1
def frostT (r p:ℕ):=2*r+p
variable {R:ℕ} {L T:Sonnet N}
lemma pair (u₁: Sonnet.Cost j r d M ε ξ C σ L) (u₂:Sonnet.Cost j r d M ε ξ C σ T)
 (q:frostT r p<separation L.o T.o):Distant (p+1) L.S T.S:=by
 intro x hx y hy
 obtain ⟨a,t,v⟩:= halo_spec.mp (u₁.tight hx)
 rw [mem_singleton] at t; subst a
 obtain ⟨b,t,w⟩:= halo_spec.mp (u₂.tight hy)
 rw [mem_singleton] at t; subst b
 have qa:=separation_triangle L.o x T.o; have qb:=separation_triangle x y T.o
 rw [separation_comm] at w; unfold frostT at q; omega

lemma graceStamp {j r p:ℕ}
 (L:Sonnet N)(h:L.Cost j r d M ε ξ C σ) (i:Axis)(z:ℤ)
 (q:L.o∈Buffered.band N i z (frostD R r p)): AtSupport false (Buffered.band N i z R) L.x:=by
 refine h.owner.mono (h.tight.trans ?_)
 intro x hx
 obtain ⟨a,t,v⟩:=halo_spec.mp hx; rw [mem_singleton] at t; subst a
 exact Buffered.band_pad i z (by unfold frostD; omega : R+r ≤ frostD R r p) (halo_spec.mpr ⟨_,q,v⟩)


variable {w s i k:ℕ}
def flurry (B:Side)(R r p w:ℕ)(θ:ℝ):Prop:=
  frostD R r p≤ spanSites B w ∧
  Again.plusAgain B (frostD R r p)≤2*spanSites B (2*w) ∧
   θ*↑((8*spanSites B (2*w))^4:ℕ)≤(1:ℝ)
open Tower
local notation "N'" => count Y s i
local notation "K₀" => tent Y H
local notation "male" => (gram Y s i k).J.M
lemma snowRate
 (hσ:0<σ) (hθ:0<θ)
 (Vv:flurry P.block (K₀).ℓ r p w θ)
 (hh:HaloTw P.K.j N')
 (h : ∀ (I:Type) [LinearOrder I] [Fintype I], ∀ (L:Finset I) (F:I→Buffered.Mark (count Y s i))(S:I→Finset (Seat (count Y s i)))(o:I→Seat (count Y s i)), 
   (∀ v∈L, LocalTune P.K.j (180*d) r ε ξ C σ (count Y s i) male (F v) (o v) (S v))→ (∀ x∈L,∀ y∈L,x≠y→Distant (p+1) (S x) (S y))→ BrokenMark Y s i k (cartMark L F) ≤ Real.exp (θ* sites (count Y s i)+ L.card* Real.log σ))

 (L:List (Sonnet N'))(u:Sylvan P.K.j r d p male ε ξ C σ L)
 (ct:(More N').val^4 ≤ L.length*(8*spanSites P.block (2*w))^4):
 ‖Journey.compass Y i k s (buffet L)‖≤ (Real.exp 1*σ)^L.length:=by
 let n:=L.length; let N:= count Y s i;
 have ht':θ * sites N ≤ n:=by
    let Z:= 8*spanSites P.block (2*w)
    have hp:θ * ↑(Z^4) ≤ 1:=Vv.2.2
    have hl:sites N ≤ ↑(n*Z^4):=by unfold sites; exact_mod_cast ct
    have hg:=mul_le_mul_of_nonneg_left hl hθ.le; have hx:=mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α:=ℝ) n); push_cast at hg hx; linarith only [hg,hx]
 let V(i':Fin n):=L.get i';
 refine (broken_ratio Y i s k (buffet L)).trans ?_
 rw [striking L]; apply le_trans (h (Fin n) _ _ (Sonnet.S∘ V) (Sonnet.o ∘ V) ?_ ?_)
 · rw [mul_pow,←Real.exp_nat_mul,show σ^L.length=Real.exp ((n:ℝ)*Real.log σ) from (by rw [Real.exp_nat_mul,Real.exp_log hσ]), ←Real.exp_add]; rw [mul_one,Finset.card_univ,Fintype.card_fin]; exact Real.exp_le_exp_of_le (add_le_add ht' (le_refl _))
 · intro i v; exact (u.core (V i) (List.get_mem L i)).issued hh.1
 intro i _ j _ h; rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne h) with t|t; exact u.annex.rel_get_of_lt (show i < j from t); exact Distant.symm (u.annex.rel_get_of_lt (show j < i from t))

lemma snow_sparse (hσ:0<σ)
 (g:Ferry Y s i k) (hw:0<w) (hw':flurry P.block (K₀).ℓ r p w θ)
 (rate:∀ L:List (Sonnet N'), Sylvan P.K.j r d p male ε ξ C σ L →
   (More N').val^4 ≤ L.length*(8*spanSites P.block (2*w))^4 →
   ‖Journey.compass Y i k s (buffet L)‖≤ (Real.exp 1*σ)^L.length)
 (hh:HaloTw P.K.j N')
 (a:Axis)
 (f:Buffered.Family K₀) (t:TestFamily K₀ true f)
 (S:Finset (Seat N'))
 (q: Sonnet.Cost P.K.j r d male ε ξ C σ ⟨distribute Y H s i f,S,0⟩):
 SparseAt Y H s i k g a (2*w) (SlabMark.relocate K₀ a w f) (Real.exp 1*σ):=by
 let D:= frostD (K₀).ℓ r p
 let B:= frostT r p
 let y:=gaugeT K₀ w
 let α:= {A:Sonnet N' // A.Cost P.K.j r d male ε ξ C σ}
 let pick: α→ Sonnet N':=fun x=>x.val
 let ρ: α→Seat N':=fun x=> x.val.o
 let δ: α→Buffered.Mark N':= fun x=>x.val.x
 let χ(a:Axis)(b:ℤ)(x:α) : α:= ⟨(x.val).twistL a b,x.prop.reflect hh ..⟩
 let e:α:= ⟨⟨distribute Y H s i f,S,0⟩,q⟩
 let seed := χ a y (χ a 0 e)
 refine ⟨N',1,(2*w),D,B,α,ρ,χ,δ,seed,
   (by omega),zero_lt_one,(one_mul _).symm,(one_mul _).symm,?_,hw'.2.1,?_,?_,?_⟩
 · refine ⟨fun i v t=>rfl,fun t=>t.prop.owner.mono (subset_univ _),
    by unfold D B frostT frostD; omega,?_,?_,?_⟩
   · intro j z x v
     rw [Nat.cast_one,one_mul]
     exact graceStamp (R:=(K₀).ℓ) (pick x) x.prop j z v
   · intro j z x
     rw [Nat.cast_one,one_mul]; rfl
   intro j z h
   rw [Nat.cast_one,one_mul]
   exact (revive Y H s i k g) j z h
 · rw [←mirror_at K₀ a (show y - 0=gaugeT K₀ w from sub_zero _) t]
   unfold Tower.mirror distribute
   -- distribute definition?
   rw [(ship_arith _ _ 0 0).2.2.2.2,(ship_arith _ _ 0 0).2.2.2.2]
   rfl
 · have he:2*y = ruler P.block*w:= ruler_offset K₀ w
   have hw₁:(D:ℤ)≤2*y:= by rw [he,spanShift]; exact_mod_cast hw'.1
   refine ⟨2*y,?_,by omega,?_⟩
   · change _=((plane a y).anon (count Y s i) ((plane a 0).anon (count Y s i) 0)) a
     rw [eq_add_of_sub_eq (across_coord ..),eq_add_of_sub_eq (across_coord ..)]
     change _ = -((-(0 - _) + _) - _) + _
     push_cast; ring
   push_cast
   linarith only [he,hw₁]
 intro A v c
 have lq:Sylvan P.K.j r d p male ε ξ C σ (A.map pick):=by
    refine ⟨?_,List.pairwise_map.mpr (v.imp (fun {x y} t => pair (L:=pick x) (T:=pick y) x.prop y.prop t))⟩
    intro e t
    obtain ⟨x,w,rfl⟩:=List.mem_map.mp t
    exact x.prop
 have he:=rate (A.map pick) lq ((by rwa [List.length_map]))
 unfold buffet at he
 rw [List.length_map,List.map_map] at he
 exact he
end Frost
