import YM.SU5.LitCurrent.Forest
import YM.CF.Buffered.Probes
import YM.CF.Chaff.Pulse
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Buffered Salt
attribute [local instance] Rill.boreKSpace Rill.boreXN

abbrev inspectFoot (p:BudgetPoint)(x:Site N):Sa N := inspected (offsetMask p.B x)
lemma halo_foot (p:BudgetPoint)(x:Site N): offsetMask p.B x ⊆ inspectFoot p x:= subset_union_left
section
variable {p:BudgetPoint}{K:Scree.Loom N}{t u:ℝ}{k q:ℕ}

structure Checked (p:BudgetPoint) (K:Scree.Loom N) (t d a:ℝ)(k q:ℕ): Prop where
 roof : Roof N t d q K
 angle : 0<d
 threshold:p.threshold ≤ t
 hint:0<a
 extra:k+q+10 ≤ p.B

-- retain yields a masked physical matrix kernel, on genuine ONLY-first Pane. Argument
-- to the projection internal: use any one tag for completion. Below pay equality even on
-- non-injective or tied tags as long as that mask passes.
variable (x:Site N)(E:StageTree N d (4*a) v)
def live (K:Scree.Loom N)(p:BudgetPoint)(k:ℕ)(x:Site N)(E: StageTree N d (4*a) v)(V:Pane N):Op (Single N):=
 Set.indicator {V|pingS p.threshold (offsetMask p.B x) V}
   (fun U=>beforePing E k (profile (K (U,Classical.arbitrary (Ids N))))) V
local notation "F"=> live K p k x E
variable (z:Checked p K t d a k q)(h:moored (node x) E)
local notation "S"=>offsetMask p.B x
local notation "L"=> roller z.angle z.roof
include z h
lemma reachesHead (D:Sa N)(i j:Single N)(g:D.card<k)(w:E.W D i j≠0): halo (q+10) D ⊆ S:=by
 have hp:node x∈D:=by by_contra H; exact w (by rw [h D H]; rfl)
 obtain ⟨X,t,e⟩:= ((E.coat D|>.1 ()).expo i j).triggered w
 intro l hl; obtain ⟨c,y,p⟩:=halo_spec.mp hl; have hu:separation (node x) c<D.card := X.lim _ hp c y
 exact halo_spec.mpr ⟨node x,mem_singleton_self _, (separation_triangle _ c _).trans (by have h':= z.extra; omega)⟩
lemma reaches_walk (D:Sa N)(i j:Single N)(g:D.card<k)(w:E.W D i j≠0)(U:Orbit N)(u: pingS p.threshold S U.1):
    Agrees D (K U) U.1:=by
 let R:Aura N:= ⟨S,⟨node x, halo_subset _ _ (mem_singleton_self _)⟩⟩
 intro a t' _; exact fern (X:=R) z.roof z.threshold D (reachesHead x E z h D i j g w) _ ⟨by rw [sdiff_empty]; exact u,empty_subset _⟩ _ t' rfl U.2

/- Even an arbitrary Openc profile with these local links can read this mask, no
   Path/travel assumption. Compare via Suite from the same library. -/
variable {F' : Openc (More N) d}{V' : Pane N}
lemma runs (U:Orbit N)(u:pingS p.threshold S U.1)(V:Pane N)(y:Openc (More N) d)(t:y.val=profile V)
    (w:∀ (D:Sa N) i j,D.card< k→ E.W D i j≠0 → Agrees D U.1 V):
    beforePing E k (profile (K U))=beforePing E k y.val:=by
 let l:= L U; rw [show profile (K U)=l.val from rfl]; rw [beforePing,beforePing,dif_pos l.property,dif_pos y.property]
 apply sum_congr rfl; intro i _; split <;> rename_i g
 · ext j m; have he:=(E.coat i|>.1 ()).expo j m
   by_cases v:E.W i j m=0
   · rw [show E.F i () l j m=0 from norm_le_zero_iff.mp ((he.bounded _).trans_eq v),show E.F i () y j m=0 from norm_le_zero_iff.mp ((he.bounded _).trans_eq v)] -- definitional y
   have hx:= w i j m g v; have ht:= reaches_walk x E z h i j m g v U u
   apply sub_eq_zero.mp; apply norm_le_zero_iff.mp
   have hm:=he.variation l y; apply hm.trans_eq; rw [show (forum N d).eval i l y=0 from ?_,mul_zero]; change fare i _ _/_=0; rw [t]; unfold fare; rw [Finset.sum_eq_zero]; swap
   · intro a p; obtain ⟨k,w⟩:= (mem_filter.mp p).2
     have hv: K U a= V a:= (ht a k w).trans (hx a k w)
     change ‖profile (K U) a-profile V a‖=0; rw [show (profile (K U)) a=(profile V) a from (funext fun i=>by unfold profile; rw [hv]),sub_self,norm_zero] -- format
   exact zero_div _
 rfl
lemma passTwo (U V:Orbit N)(u:pingS p.threshold S U.1)(v:pingS p.threshold S V.1)(g:Agrees S U.1 V.1):beforePing E k (profile (K U))=beforePing E k (profile (K V)):=by
 refine runs x E z h U u (K V) (L V) rfl ?_
 intro D i j t p
 have he:D⊆S:= (halo_subset (q+10) _).trans (reachesHead x E z h D i j t p)
 have hv:= reaches_walk x E z h D i j t p V v
 exact fun i t u=> (g i (he t) (he u)).trans (hv i t u).symm
lemma noTag (U:Orbit N): F U.1 = if pingS p.threshold S U.1 then beforePing E k (profile (K U)) else 0:= by
 unfold live; split <;> rename_i g; rw [Set.indicator_of_mem (show U.1∈_ from g)]; exact passTwo x E z h _ _ g g (fun _ _ _=>rfl); exact Set.indicator_of_notMem g _
lemma live_local : LocalOn (inspectFoot p x) F:=by
 intro U V u; let X:Orbit N :=(U,Classical.arbitrary _); let Y:Orbit N:=(V,Classical.arbitrary _); have hp: pingS p.threshold S X.1 ↔ pingS p.threshold S Y.1:= Chaff.fenceW _ u _
 change F X.1= F Y.1; rw [noTag x E z h, noTag x E z h]; split <;> rename_i g; · rw [if_pos (hp.mp g)]; exact passTwo x E z h X Y g (hp.mp g) (agrees_mono u (show (S:Set (Seat N))⊆inspectFoot p x from halo_foot p x))
 rw [if_neg (mt hp.mpr g)]
lemma modes_pass (U:Orbit N) : cutM (modesIn N S)* F U.1 * cutM (modesIn N S) = F U.1:=by
 rw [noTag x E z h]; split <;> rename_i g; swap; · simp
 let V:= L U; rw [show profile (K U)=V.val from rfl]; unfold beforePing; rw [dif_pos V.property]
 unfold retain; rw [mul_sum, sum_mul]; apply sum_congr rfl; intro D _; split_ifs with w; swap; · simp
 ext i j
 let Y:= E.F D () V; unfold cutM; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
 change (_ * Y i j)* _=Y i j
 by_cases v:Y i j =0; · rw [v]; simp
 have hU:= (E.coat D|>.1 ()).expo i j; have hp:E.W D i j≠ 0:=fun k=> v (norm_le_zero_iff.mp ((hU.bounded V).trans_eq k)); have ht:D⊆ S:= (halo_subset _ _).trans (reachesHead x E z h D i j w hp)
 rw [if_pos (show i∈ modesIn N S from (modes_at ..).mpr (ht (hU.triggered hp).2.1)),if_pos (show j∈ modesIn N S from (modes_at ..).mpr (ht (hU.triggered hp).2.2)),mul_one,one_mul]
lemma glyphMove (U:Pane N)(g: Seat N→ SU.E): F (Lattice.gauge g U)=twist (tradew N g) (F U):=by
 let y:Orbit N:=(U,Classical.arbitrary _); let V:Orbit N:=(Lattice.gauge g U,threadG g y.2)
 change F V.1=twist (tradew N g) (F y.1); rw [noTag x E z h,noTag x E z h]; have hg:pingS p.threshold S V.1↔pingS p.threshold S y.1:=pingB y.1 g
 by_cases u:pingS p.threshold S y.1; swap; · rw [if_neg u,if_neg (mt hg.mp u),map_zero]
 rw [if_pos u,if_pos (hg.mpr u)]; let X:=L y
 change beforePing E k (L V).val=twist (tradew N g) (beforePing E k X.val); rw [beforePing,beforePing,dif_pos (L V).property,dif_pos X.property]
 unfold retain; rw [map_sum]; apply sum_congr rfl; intro Uc _; split_ifs with q
 · let T:= (forum N d).drive g X; change E.F Uc () (L V)=_; rw [show L V=T from roll_g z.angle z.roof g y, Inter.frame (E.coat Uc|>.1 ()).toTicket.frame g X, twist_formula]; rfl
 exact (map_zero ..).symm
lemma norm_pass (U:Pane N): ‖F U‖ ≤ expiry (4*a) v:=by
 have ht:= (totals E z.hint h k).1.pay; unfold live Set.indicator; split <;> rename_i u; · exact norm_U ht z.hint.le (L (U,Classical.arbitrary _))
 rw [norm_zero]; exact soakCostNN ht
lemma enve_pass : Envelope F:=by
 refine ⟨?_, expiry (4*a) v, norm_pass x E z h⟩
 let Y(U:Pane N):= (U,(Classical.arbitrary (Ids N)))
 have hp: Measurable (fun U:Pane N=>retain E k (L (Y U))):=(show Continuous (retain E k) from ?_).measurable.comp ((roll_m z.angle z.roof).comp (measurable_id.prodMk measurable_const))
 · unfold live; apply Measurable.indicator _ (ping_o.measurableSet); change Measurable (fun U:Pane N=>beforePing E k (L (Y U)).val); rw [show (fun (U:Pane N)=> beforePing E k _)=(fun U:Pane N=> retain E k (L (Y U))) from funext fun x=> dif_pos (L (Y x)).property]; exact hp
 unfold retain; refine continuous_finsetSum _ fun i _=>?_ ; split; exact ((E.coat i).1 ()).toTicket.cont; exact continuous_const

end
end YM.CF.LitCurrent
