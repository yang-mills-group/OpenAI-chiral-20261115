import YM.SatinExist.Zanthe
import YM.SatinExist.CeladonA
import SatinThinFusionApplied
import YM.SU5.FiniteGaugeData.Steam.Away
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
open CF.Lamour.Bridge.Celeste Sonnet Rutabaga
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

open SpotP CF.Velvet Aria
variable (s:ℕ)(F:P.Test)
/-- Only on the testing path here. no all heights-cost. -/
abbrev EvSmall := ∀ᶠ i:ℕ in atTop, SpotP.SmallG (distribute Ψ H s (P.nomadic i) F.val)
abbrev Lax (C:ℝ) : Prop:= ∀ᶠ s:ℕ in atTop, ∀ᶠ i:ℕ in atTop, ∀ k:ℕ, (P.run.voyage i).kick≤k → s≤P.run.uv k → Yoke.ShelterCost C P.run s i k
variable (u:P.Lax C)
include u
open CF Pressure Pressure.Worth Worth.Pays
private lemma igloos (z:ℝ)(p:0<z): ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop, ∀ k:ℕ,(P.run.voyage i).kick≤k→s≤P.run.uv k→ Rutabaga.knownM Ψ i k s 0 0 0 0 0 1 z:=by
 have ht:= ((BProof.coin_purchases («b»:=0) (c:=0) (Or.inl (by norm_num [r_meter]:r_meter<0))): Tendsto meterC atTop (𝓝 0))
 have hm:= ht.comp (Steam.horizons P.par.x (V:=P.par.V)); filter_upwards [hm.eventually (ge_mem_nhds (show 0<z/14 from by positivity)),u] with s h u'
 filter_upwards [u'] with i v k x p A d
 let Y:=side Ψ i s; have hp:=Yoke.marketIgloo Ψ s i k (v k x p) (z:=0) x d.occupy.env (show ∀ V:Orbit Y,_ from fun V=> let a:=SpotP.larder A d (V.1,(P.run.voyage i).CapeT s V); (by simpa only [Real.exp_zero] using a))
 refine hp.trans (Real.exp_monotone ?_); rw [zero_add]; -- cost cine
 let w:= (P.par.R.L); have ht:14 * meterC (hat P.par.R.L P.par.x s)≤ z :=by apply le_of_le_of_eq (mul_le_mul_of_nonneg_left h (by norm_num)); ring
 exact (mul_le_mul_of_nonneg_right ht (show 0 ≤ sites Y from zero_le_one.trans (sites_pos Y))).trans (le_of_eq (by simp [sites,Y]))
include D
lemma pay_igloo (S:Finset Cover)(r0:ℕ):∃ (w:ℕ)(_ : r0<w),∀ᶠ s:ℕ in atTop,∀ (F:P.Test),F∈bay P.calibration S true→P.EvSmall s F→∀ (X:P.Card j s (w+w))(a:P.voxTest j s X.val=P.shifts j w F),
 ‖boxOp Ψ H P.law s P.history P.projection.clipped j false (P.room j) (w+w) X (by omega)‖ ≤ Real.sqrt (RedD+3):=by
 let S':= insert 0 S; let R0:= breadth 0 S'; let B:= 2*R0
 let w:= ℓ+R0+r0+1; have ht:r0<w:=by unfold w; omega
 have hp:0<w:=by omega
 let Q(i:Axis):ℤ:=-(R0:ℤ)
 let γ:=volumePrice W (w+w) B; have hγ:0<γ:=by unfold γ volumePrice; have f:0<P.calibration.B.val:=P.calibration.B.property; have ht:0<B+addgap W:=Nat.add_pos_right _ addgap_pos; positivity
 let η:=(γ:ℝ)⁻¹; have hη:0<η:=by unfold η; positivity
 refine ⟨w,ht,?_⟩
 filter_upwards [igloos P C u _ hη] with s hM F hf sm X α
 have hf':= ((show InTest W true S false F.val from hf).mono (subset_insert (0:Cover) S)) -- adjust
 obtain ⟨R',aR,hb⟩:= X.property
 obtain ⟨L,hL⟩:= valuation Ψ H aR; let l:=L+1; have hl:0<l:=add_pos_of_nonneg_of_pos (pay_nonneg (F:=X.val.val) hL) one_pos;
 refine onship_paid_eight Ψ H P.law s P.history j false (P.room j) (w+w) X P.projection.clipped (add_pos hp hp) (fun _=>X.val.val) (BQueue.stay aR hl (fun i y=>(hL i y).trans (by unfold l; linarith))) hb RedD ?_
 constructor; · unfold RedD; positivity
 have hd:Tendsto (fun i=>count Ψ s (P.nomadic i)) atTop atTop:=tendsto_atTop.2 (fun y=> (P.amount_go s).eventually_ge_atTop y.val);
 have hz:Tendsto (fun i=>(↑(count Ψ s (P.nomadic i)).val:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp (P.amount_go s)
 let τ:= distribute Ψ H s
 filter_upwards [D s,P.history.finance s,(P.amount_go s).eventually_ge_atTop (B+addgap W),hz.eventually_ge_atTop (1*(16/Rutabaga.Yθ)),(P.law.pick.grow_i.tendsto_atTop.comp P.history.growsA.tendsto_atTop).eventually hM,sm, hd.eventually (ownsHalo (j:=P.par.K.j) (by rw [P.par.kJ]; decide)),hd.eventually (breadthMoney 0 S')] with i eI fer Vb Hb ear pa Halo Bread m hm Li Ri
 let n' := P.nomadic i; let i':= P.engine i; let N:=side Ψ n' s; let M:= (gram Ψ s n' i').J.M; have hv:Even N.val:=Vale.val_e ..
 have Hc: HaloTw P.par.K.j N:= Halo hv
 refine Rutabaga.ticket Ψ H 0 0 1 η i' fer eI Hc (ear i' fer.depth fer.enters) hη.le ((inv_mul_cancel₀ (show (γ:ℝ)≠0 by positivity)).le) X.val.val Q j ?_ (add_pos hp hp) Vb zero_le_one Hb hm Li Ri
 let K:=τ n' F.val
 let A:=Sonnet.mk K (dBook N S') (wrap (More N) 0); have he:CupC P.par.K.j 0 0 M 0 0 1 1 A:= ⟨stationed Ψ H s S' n' hf',mem_image_of_mem _ (mem_insert_self ..),pa⟩
 have hs: (ℓ:ℤ)+R0≤ b*w:=by have hz: (w:ℤ) ≤ b*w:= le_mul_of_one_le_left (by exact_mod_cast hp.le) (ruler_gene _); unfold w at *; omega
 have hr:Rutabaga.Start j Q (τ n') P.par.K.j 0 0 0 M 0 0 1 1 B (-(b*w)) (b*w) 1  F.val:=by
    have ha (p:Seat N)(x:p ∈ Broad 0 [A]) (i:Axis): Chord (Q i) B (p i):=by
       have hu:p∈Lattice.halo 0 A.S:= by simpa using x
       apply oneSeat (a:=p) -- tune binder
       have he':= show p∈BlockP (R0+0) A.o from Lamour.Bridge.fit Bread (show p∈Lattice.halo 0 (dBook N S') from hu)
       change p∈ BlockP _ (wrap (More N) 0) at he'; rw [Nat.add_zero,map_zero] at he'; exact he'
    refine ⟨[A],⟨SpotP.Sylvia.one he,fun i t=>?_,fun a v i p=> ha i p a⟩,rfl,?_⟩
    · obtain ⟨b',q,v',r⟩:= ha i t j; have hx:(tent Ψ H).ℓ=P.calibration.ℓ:=rfl; refine ⟨b',?_,?_,r⟩ <;> unfold Q B at * <;> omega
    rw [buffet_more,buffet_empty,mul_one]
 have hl₀:= distribute_arith Ψ H s n'
 have hw:= Rutabaga.Start.addRoom j Q (τ n') (fun B' F=>(hl₀ F F 0).2.2.2.2 _ _) Hc hr w
 have hv0:X.val.val= relocate W j (w:ℤ)  F.val:=congrArg Subtype.val α
 rw [hv0]; rw [show (tent Ψ H).B=P.calibration.B from rfl, add_neg_cancel, ← mul_add, ←Nat.cast_add] at hw; exact hw
open Casting
lemma liberal (S:Finset Cover): ∀ᶠ s:ℕ in atTop,∀ (x:P.Spectrum0 j)(F:P.Test), F∈enclave W→ F∈bay W S true→ P.EvSmall s F → ‖P.singleState j s x F‖ ≤ Real.sqrt (RedD+3):=by
 obtain ⟨a,q⟩:=eventually_atTop.1 (P.card_slack j S); obtain ⟨w,g,f⟩:=P.pay_igloo j C D u S a -- parameter order
 have hp:0<w+w:=by omega
 filter_upwards [f] with s t x F p f ps
 let V:= P.shifts j w F; let L:=plow W j w S
 have hb:= (Between.relocate W j (q w g.le) (w:ℤ)); -- tune
 rw [neg_mul,show ruler (W).B = ruler P.par.block from rfl,add_neg_cancel,←mul_add, ←Nat.cast_add] at hb; let k:= P.shifts_support j w S f
 let U:= P.colorSpace j x; let Yb:P.Card j s (w+w):= ⟨P.positiveVox j s L V k (fun p t=> (hb p t).1),L,k,hb⟩
 have hx:P.voxTest j s Yb.val = V:= rfl; have hu:= P.shifts_keep j (w:ℤ) p
 let Ω:=P.colorZero j x; let J:= P.door j s (w+w) hp Yb hu; let F':=(U J)
 have hy: ‖F'‖ ≤ Real.sqrt (RedD+3):= (NonUnitalStarAlgHom.norm_apply_le U J).trans (t F f ps Yb rfl)
 have hz: ‖Ω‖=1:=P.norms_color j x; rw [← P.slide_single j x s w F,← show P.voxTest j s Yb.val = P.shifts j (w:ℤ) F from hx,←P.view_scalar j x s (P.admitted_view j s Yb hu),←P.attended]; exact (norm_inner_le_norm ..).trans ((by rw [hz,one_mul]; exact (F'.le_opNorm Ω).trans (by rw [hz,mul_one]; exact hy)))
#print axioms liberal
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
