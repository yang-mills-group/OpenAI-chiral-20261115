import YM.SU5.FiniteGaugeData.Trigonal.Tortoise
/-! # Color-specific tilted contract. Arbitrary many-body. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "X"=> Trigo.Chamber true -- Window opened
local notation "Y₀"=> Trigo.Chamber false
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
variable (f:Fin n→Trigo.Chamber true)(g':Fin n→Trigo.Chamber false)
local notation "L"=> Torte f g'
variable {S:Finset Cover}{N m':Side}(K':Calibration)
abbrev Creates(x:X)(p:SU.Slot):Family K':= creation K' x.1 x.2.val p
abbrev Removes(x:Y₀)(p:SU.Slot):Family K':= removal K' x.1 x.2.val p
abbrev footprint {b:Bool}(f:Fin n→ Trigo.Chamber b):Finset Cover:= univ.image fun i=>nodeC (f i).1
abbrev Might(K:Calibration)(x:Δ): Family K := Creates K (f (collar n x).2) (collar n x).1*Removes K (g' (collar n x).2) (collar n x).1
lemma TorteV : Torte f g' K'= (List.ofFn (Might f g' K')).prod:=by
 have hp {ι:Type}(z:List ι) (w:ι→Family K')(m:Side)(u:Fields (K'.c m)) :(z.map w).prod m u=(z.map (fun i=> w i m u)).prod:=by induction z with| nil=>rfl| cons z y ih => change _*(y.map w).prod m u=_*_; rw [ih]; rfl
 funext m u; rw [←show (List.ofFn id).map (Might f g' K')= (List.ofFn (Might f g' K')) from (by rw [List.map_ofFn,Function.comp_id]), hp,List.map_ofFn]; rfl
variable (p:footprint f⊆ S)(t: footprint g'⊆ S)
include p t
lemma tote : InTest K' false S false (Torte f g' K'):= by
 have he(i:Δ): InTest K' false S false (Might f g' K' i):=by
    let a:= f (collar n i).2; let b:= g' (collar n i).2
    have ht(x:Fin n): nodeC (g' x).1∈ S:= t (mem_image_of_mem _ (mem_univ x))
    exact InTest.mul (.creator _ (f (collar n i).2).2.property (p (mem_image_of_mem _ (mem_univ _)))) (.remover _ (mem_compl.mp b.2.property) (ht _))
 have hf(l:List Δ): InTest K' false S false (l.map (Might f g' K')).prod:=by induction l with | nil => exact .one | cons a X₁ ih=> exact (he a).mul ih
 rw [TorteV,←show (List.ofFn id).map (Might f g' K')= (List.ofFn (Might f g' K')) from ?_]; · exact hf _
 rw [List.map_ofFn, Function.comp_id]
omit p t
lemma TorteW : Torte f g' K'∈ Charm.well K':= ⟨⟨⟨footprint f∪footprint g', (tote f g' K' subset_union_left subset_union_right).widen⟩,by simp⟩,fun n v _=> (inscribed f g' v).symm⟩
def Base(K:Calibration): W K:= ⟨Torte f g' K, TorteW f g' K⟩
abbrev paper (f:Fin n→Trigo.Chamber true)(g:Fin n→Trigo.Chamber false): Paint:= fun N _=>TextK f g N
lemma weight_q{b:Bool}(i:Trigo.Chamber b)(N:Side)(p:SU.Slot):‖quantum N i p‖=1:=by unfold quantum basisC; rw [norm_smul]; unfold Lifted.winding; rw [Rush.fee_norm,one_mul]; simp [basisKet]
lemma costO{b:Bool}(p:Trigo.Chamber b)(v:SU.Slot)(g:nodeC p.1∈S): Ram (modesIn N (region S N)) (quantum N p v):=by unfold Ram Upt quantum basisC; rw [map_smul]; refine congrArg (fun v:Ket _=> _ • v) (within_basis _ _ ?_); refine (modes_at ..).2 (?_ ); change node (wrap N p.1)∈ region S N; rw [node_of]; exact mem_image_of_mem _ g
lemma LF (x:X)(v: SU.Slot): Upt (tickA N) (quantum N x v):=by rw [touchP]; unfold Upt quantum basisC; rw [map_smul]; exact congrArg (fun (t:Ket (Single N))=> Lifted.winding N x.1 • t) (within_basis _ _ (highZ x v))
lemma BF (x:Y₀)(v: SU.Slot): Upt (1-tickA N) (quantum N x v):=by rw [touchP,←dim_cut]; unfold Upt quantum basisC; rw [map_smul]; exact congrArg (fun (t:Ket (Single N))=> Lifted.winding N x.1 • t) (within_basis _ _ (mem_compl.mpr (lowZ x v)))
private lemma AuthZ {c b:ℝ}(f:Fin m→FC (Single N))(h:∀ i, Art c (tickA N) (modesIn N (region S N)) false (f i) b): Art c (tickA N) (modesIn N (region S N)) false (rollF f) ((2*b)^m):=by
 induction m with
 | zero=> simp only [pow_zero,rollF,List.ofFn_zero,List.prod_nil]; exact .lone
 | succ m ih=> unfold rollF; rw [List.ofFn_succ,List.prod_cons,pow_succ']; exact .work (b:=false) (a:=false) (h 0) (ih (fun i=> f i.succ) (fun i=>h _)) -- tune `.work` fields.
include p t
lemma veteran (h:S.Nonempty):Auth K' S (Base f g' K') (paper f g'):= by
 refine ⟨(tote f g' K' p t).widen,fun i=>rfl,h, fun i g _=> (inscribed f g' _).symm,fun H v=> ?_, fun H v ε e=> ⟨1, zero_lt_one,fun N U _=>?_⟩⟩; swap; · unfold paper; rw [sub_self]; exact (Art.hid _).pump e.le
 let b:= 2*H*H; have hp:0<b:=mul_pos (mul_pos two_pos (zero_lt_one.trans_le v)) (zero_lt_one.trans_le v); refine ⟨(2*b)^(projCard n),by positivity,fun N U=>AuthZ _ fun i=>?_⟩; change Art H (tickA N) _ _ (Umo f N i*Bmo g' N i) b; let a:= f (collar n i).2; let x:= g' (collar n i).2; let v:= (collar n i).1; have hX:nodeC (f (collar n i).2).1∈S:= p (mem_image_of_mem _ (mem_univ _)); have hy:nodeC (g' (collar n i).2).1∈S:=t (mem_image_of_mem _ (mem_univ _))
 let W:=quantum N a v; let w:=quantum N x v; have ht:b=2*(H*‖W‖)*(H*‖w‖):=by unfold b W w; rw [weight_q,weight_q]; ring
 rw [ht]; exact (Art.chor W (LF a v) (costO a v hX)).work (Art.thal w (BF x v) (costO x v hy))
#print axioms veteran
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
