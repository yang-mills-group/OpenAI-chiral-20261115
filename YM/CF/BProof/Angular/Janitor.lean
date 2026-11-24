import YM.CF.BProof.Angular.Layout

/- Combining gap and N sweep with free tags to get flattened gauge integrals. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular.Yard
open Function Lattice Gauge Mag CF.BProof.Face SU MeasureTheory Wilson Finset Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group
variable {s : Side} (Y : Yard s)(i:Y.Index)(x:Per s)(p:Space s)(U:Config G s)

def gapGauge (r:Site s) := sweep (Y.v i) (time r) (space r) U (if Y.D i then 0 else Y.short) 1
abbrev location (b:Bool) := if b then i else i-1
/-- nGauge for the combined operation, sweep out from frames inherited from gap. -/
def nFrame : Eyes s:= fun b p=> Y.gapGauge (Y.location i b) U (join (front (Y.u i) Y.long b) p)
def nGauge := stage (Y.u i) Y.long U (Y.nFrame i U)
def bGauge : Site s→E:= if Y.D i then 1 else Y.nGauge i U

def janitor (r:Site s): E := let x:= time r; if Y.Band (Y.twinsBand x) x then Y.bGauge (Y.twinsBand x) U r else Y.gapGauge (Y.twinsGap x) U r
lemma jan_in_band (r:Site s)(h:Y.Band i (time r)): janitor Y U r=Y.bGauge i U r:=by unfold janitor; dsimp only; rw [Y.u_part _ _ h,if_pos h]
lemma gFrame (b:Bool)(h:¬Y.D i) : Y.nEnd (Y.location i b)=front (Y.u i) Y.long b:=by
 cases b <;> unfold nEnd location <;> simp only [Bool.false_eq_true,↓reduceIte,front_left,front_right,(Y.prev i).mpr h,h,sub_add_cancel]
 exact (Y.last_pole _).symm
lemma gap_start (r:Site s)(h:time r=Y.dEnd i): Y.gapGauge i U r=1:=by
 unfold gapGauge; rw [h]; unfold dEnd; split; apply sweep_base; rw [along_self]; apply sweep_base; exact Y.v_in i -- split semis
lemma jan_in_gap (h:Y.Gap i x) : janitor Y U (join x p)=gapGauge Y i U (join x p):=by
 unfold janitor; dsimp only [time_join]; split; swap; next hv=> rw [Y.v_part i x h]
 next H=>
  generalize hu:Y.twinsBand x = j at *; unfold bGauge; split
  · rename_i hz; refine (gap_start Y i U _ ?_).symm
    rcases Y.common j x H h with ⟨hh,hg⟩|⟨hh,rfl⟩; rw [time_join,hh,dEnd,if_neg ((Y.next i).1 (hg ▸ hz)),hg]; exact (by rw [time_join,dEnd,if_pos hz]; exact hh)
  rename_i hz; unfold nGauge; rcases Y.common j x H h with ⟨hh,hg⟩|⟨hh,rfl⟩
  · have he:i=Y.location j false:= (by simp [location,hg]); have hv:x=front (Y.u j) Y.long false:=hh.trans (front_left ..).symm; rw [hv,stage_set (Y.u j) _ _ _ false p Y.long_pos (by have :=Y.lL; omega)]; unfold nFrame; rw [← he]
  have he:x=front (Y.u i) Y.long true:=hh.trans (Y.last_pole _).symm; rw [he,stage_set (Y.u i) _ _ _ true p Y.long_pos (by have := Y.lL; omega)]; exact rfl
@[fun_prop] lemma gapGauge_m : Continuous (Y.gapGauge i) := by apply continuous_pi; intro r; unfold gapGauge; fun_prop
@[fun_prop] lemma nFrame_m : Continuous (Y.nFrame i) := by apply continuous_pi; intro b; apply continuous_pi; intro p; unfold nFrame; fun_prop
@[fun_prop] lemma nGauge_m : Continuous (Y.nGauge i) := by unfold nGauge; exact (stage_m (Y.u i) Y.long).comp (f:=fun U:Config G s=>(U,Y.nFrame i U)) (continuous_id.prodMk (nFrame_m Y i)) -- tune
@[fun_prop] lemma jan_c : Continuous (janitor Y) := by apply continuous_pi; intro r; unfold janitor bGauge; dsimp only; split_ifs <;> fun_prop

variable {U}
def Frozen (a:Site s→E) := ∀ i, Y.D i→ Set.EqOn a 1 (Y.band i)
lemma janitor_frozen (U:Config G s) : Y.Frozen (Y.janitor U):=by intro i h r k; rw [Y.jan_in_band i U r (mem_strip.mp k),bGauge,if_pos h]
lemma trunk_b (p:Space s){i:Y.Index}{x:Per s}(h:¬Y.D i)(hp:along (Y.u i) x<Y.long)(hh:¬Y.Cut i x) : vert x p∈Y.trunks:= (trunk_v ..).2 (Or.inr ⟨_,h,hp,hh⟩)
lemma trunk_g (p:Space s){i:Y.Index}{x:Per s}(hp:along (Y.v i) x<Y.short) : vert x p∈Y.trunks:=(trunk_v ..).2 (Or.inl ⟨_,hp⟩)
lemma g_swept (U:Config G s)(h:along (Y.v i) x<Y.short) : Lattice.gauge (janitor Y U) U (vert x p)=1:=by
 have hx:along (Y.v i) x+1<s.val:=by have := Y.dD; omega
 unfold Lattice.gauge vert; dsimp only; rw [←join_step,jan_in_gap Y _ _ p _ h.le,jan_in_gap Y i _ p _ (by unfold Gap; rw [along_succ hx]; exact h)]; unfold gapGauge; rw [time_join,time_join,space_join,space_join,sweep_next _ _ _ _ _ hx]; exact mul_inv_cancel _
lemma b_swept (U:Config G s)(h:¬Y.D i)(hp:along (Y.u i) x<Y.long)(hh:¬Y.Cut i x) : Lattice.gauge (janitor Y U) U (vert x p)=1:=by
 have hx:along (Y.u i) x+1<s.val:=by have := Y.lL; omega
 unfold Lattice.gauge vert; dsimp only; rw [←join_step,jan_in_band Y i _ (join x p) hp.le,jan_in_band Y i _ (join (x+1) p) (by unfold Band; rw [time_join,along_succ hx]; exact hp),bGauge,if_neg h,join_step]; exact stage_normal _ _ _ _ _ hx hh _
lemma swept (U:Config G s) : Set.EqOn (Lattice.gauge (janitor Y U) U) 1 (↑Y.trunks):=by
 intro k h; rcases whichBond k with ⟨x,p,rfl⟩|⟨x,p,j,rfl⟩; swap; · exact absurd h (trunk_h Y x p j)
 rcases (Y.trunk_v ..).1 h with ⟨i,h⟩|⟨i,h,e,hp⟩; exact Y.g_swept i x p U h; exact Y.b_swept i x p U h e hp
lemma existsJanitor (X: (↑Y.trunks)→E) : ∃ a:Site s→ E,Y.Frozen a ∧ ∀ U:Config G s,(∀ b h,U b=X ⟨b,h⟩)→ Set.EqOn (Lattice.gauge a U) 1 ↑Y.trunks:=by
 let Q:Config G s:=fun b=> if h:b∈Y.trunks then X ⟨b,h⟩ else 1
 refine ⟨Y.janitor Q,Y.janitor_frozen Q,fun U h b hb=>?_⟩; convert Y.swept Q hb using 1; unfold Lattice.gauge; rw [h b hb]; simp [Q,mem_coe.mp hb]
end YM.CF.BProof.Angular.Yard
