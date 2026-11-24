import YM.SatinExist.Vertigo
import SatinThinFusionApplied
-- truly attain op budget on front conductor, WITHOUT supplying new coupling
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 340000
set_option linter.unusedSectionVars false
set_option maxRecDepth 3500
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common CF.Pannier.Chancel
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Prototype
open Lamour.Bridge.Celeste.Morn CF.Py.Rate.LocalLimit.Papal
open CF.Lamour.Bridge.Celeste Sonnet Lungo
namespace Spine
open MacroGrid
open CF.Lamour.Bridge
private lemma oneSeat {N:Side}{r:ℕ}{a:Seat N}(q:a∈BlockP r (0:Seat N))(j:Axis):Chord (-(r:ℤ)) (2*r) (a j):=by
 let Z:=Lattice.lift a
 have hp:= (component_le a j).trans (show pdist a≤ r from (by have hp:=blocks_test.mp q; rw [separation_comm,separation,sub_zero] at hp; exact hp)) -- tune
 have hv:(Z j).natAbs≤r:=hp
 exact ⟨Z j,(by omega),by omega,Eq.symm (congrFun (wrap_lift a).symm j)⟩
variable (P:Spine)(R : P.Register)(j:Axis)(C A:ℝ)(Y:Supplier)(T:uniform P R Y C A)(D:P.NightCop)
local notation "W"=>P.calibration
local notation "Λ"=>P.par
local notation "Ψ"=>P.run
local notation "H"=>P.large
local notation "ℓ"=>P.calibration.ℓ
local notation "b"=> ruler P.calibration.B
local notation "θ"=> P.tuneK
variable {w N a b':ℕ} {F:Weaver}{S:Finset Cover}(v: Lamour.Bridge.Celeste.Voice F S) (h:Clarity F P.par.K.j (1/4))
-- more-or-less any grid fixed lender. choose t large after request.
abbrev RedD := (2*Real.exp 1)^2
include T D h
open CF.Velvet
lemma pay_arena (r0:ℕ):∃ (w:ℕ)(_ : r0<w), ∀ᶠ s:ℕ in atTop,∀ (X:P.Card j s (w+w))(a:P.voxTest j s X.val=P.shifts j w (θ v)),
 ‖boxOp Ψ H P.law s P.history P.projection.clipped j false (P.room j) (w+w) X (by -- w positivity problematic
    omega)‖ ≤ Real.sqrt (RedD+3):=by
 obtain ⟨A₀,u,W₀,α,H0,pX,g,e⟩:= T.1.paper; let S':= insert 0 S
 let v':=v.mono (subset_insert (0:Cover) S)
 let r:= breadth 0 S'; let d:=S'.card
 obtain ⟨V,hV,wV⟩:= v'.1.rent; obtain ⟨n,k,g',e',t',b',Pp⟩:= choose_optic (P.par.kJ.symm ▸ (by decide : 1 ≤ (4:ℕ))) (180*d) hV (show (0:ℝ)<1 from zero_lt_one)
 let R0:= r+k; let B:=2*R0
 let w:= ℓ+R0+r0+1; have ht:r0<w:=by unfold w; omega
 have hp:0<w:=by omega
 let Q(i:Axis):ℤ:=-(R0:ℤ)
 let γ:=volumePrice W (w+w) B; have hγ:0<γ:=by unfold γ volumePrice; have f:0<P.calibration.B.val:=P.calibration.B.property; have ht:0<B+addgap W:=Nat.add_pos_right _ addgap_pos; positivity
 let η:=(γ:ℝ)⁻¹; have hη:0<η:=by unfold η; positivity
 obtain ⟨f0,vf0⟩:=T.1.nerve
 obtain ⟨x,hx,vx,F0,Hr⟩:= choose_floor P.par.K.j (by rw [P.par.kJ]; decide) (show 0< η*(8/9) from (by positivity)) Pp.zephyr;
 obtain ⟨ξ,cX,xY⟩:= ((v'.1.fee _ Pp.zephyr).and self_mem_nhdsWithin).exists
 have md:Meringue.{0} Ψ k r (180*d) e' ξ V 1 η:= salon Ψ Pp hx vx vf0 F0 (by rw [show η/9=η*(8/9)/8 by ring]; exact Hr) hη g T.2 (show 0<ξ from xY) hV zero_lt_one r
 refine ⟨w,ht,?_⟩
 filter_upwards [come Ψ H k r d e' ξ V η md] with s hM X α
 obtain ⟨R',aR,hb⟩:= X.property
 obtain ⟨L,hL⟩:= valuation Ψ H aR; let l:=L+1; have hl:0<l:=add_pos_of_nonneg_of_pos (pay_nonneg (F:=X.val.val) hL) one_pos;
 refine onship_paid_eight Ψ H P.law s P.history j false (P.room j) (w+w) X P.projection.clipped (add_pos hp hp) (fun _=>X.val.val) (BQueue.stay aR hl (fun i y=>(hL i y).trans (by unfold l; linarith))) hb RedD ?_
 constructor; · unfold RedD; positivity
 have hd:Tendsto (fun i=>count Ψ s (P.nomadic i)) atTop atTop:=tendsto_atTop.2 (fun y=> (P.amount_go s).eventually_ge_atTop y.val);
 have hz:Tendsto (fun i=>(↑(count Ψ s (P.nomadic i)).val:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp (P.amount_go s)
 let τ:= distribute Ψ H s
 filter_upwards [D s,P.history.finance s,(P.amount_go s).eventually_ge_atTop (B+addgap W),hz.eventually_ge_atTop (V*(16/Lungo.Yθ)),(P.law.pick.grow_i.tendsto_atTop.comp P.history.growsA.tendsto_atTop).eventually hM, hd.eventually h, hd.eventually (ownsHalo (j:=P.par.K.j) (by rw [P.par.kJ]; decide)),hd.eventually (breadthMoney 0 S')] with i eI fer Vb Hb ear pay Halo Bread m hm Li Ri
 let n' := P.nomadic i; let i':= P.engine i; let N:=side Ψ n' s; let M:= (gram Ψ s n' i').J.M; have hv:Even N.val:=Vale.val_e ..
 have Hc: HaloTw P.par.K.j N:= Halo hv
 refine Lungo.ticket Ψ H e' ξ V η i' fer eI Hc (ear i' fer.depth fer.enters) hη.le ((inv_mul_cancel₀ (show (γ:ℝ)≠0 by positivity)).le) X.val.val Q j ?_ (add_pos hp hp) Vb hV Hb hm Li Ri
 let A:=Sonnet.mk (F N) (dBook N S') (wrap (More N) 0); have he:A.Cost P.par.K.j r d M e' ξ V 1:= ⟨⟨wV N,cX N⟩,v'.2 N,v'.1.bounded N, card_image_le,Bread,mem_image_of_mem _ (mem_insert_self ..),pay hv M⟩
 have hs: (ℓ:ℤ)+R0≤ b*w:=by have hz: (w:ℤ) ≤ b*w:= le_mul_of_one_le_left (by exact_mod_cast hp.le) (ruler_gene _); unfold w at *; omega
 have hr:Lungo.Start j Q (τ n') P.par.K.j r d k M e' ξ V 1 B (-(b*w)) (b*w) 1 (household W F):=by
    have ha (p:Seat N)(x:p ∈ Broad k [A]) (i:Axis): Chord (Q i) B (p i):=by
       have hu:p∈Lattice.halo k A.S:= by simpa using x
       apply oneSeat (a:=p) -- tune binder
       have he':= show p∈BlockP (r+k) A.o from Lamour.Bridge.fit he.tight hu
       change p∈ BlockP _ (wrap (More N) 0) at he'; rw [map_zero] at he'; exact he'
    refine ⟨[A],⟨Sylvan.one he,fun i t=>?_,fun a v i p=> ha i p a⟩,rfl,?_⟩
    · obtain ⟨b',q,v',r⟩:= ha i t j; have hx:(tent Ψ H).ℓ=P.calibration.ℓ:=rfl; refine ⟨b',?_,?_,r⟩ <;> unfold Q B at * <;> omega
    have stay {g k:Side}(h:g=k): ship h (F g)=F k:=by subst k; rfl
    rw [buffet_more,buffet_empty,mul_one]; exact stay (terrain ..)
 have hl₀:= distribute_arith Ψ H s n'
 have hw:= Lungo.Start.addRoom j Q (τ n') (fun B' F=>(hl₀ F F 0).2.2.2.2 _ _) Hc hr w
 have hv0:X.val.val= relocate W j (w:ℤ) (household W F):=congrArg Subtype.val α
 rw [hv0]; rw [show (tent Ψ H).B=P.calibration.B from rfl, add_neg_cancel, ← mul_add, ←Nat.cast_add] at hw; exact hw
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
