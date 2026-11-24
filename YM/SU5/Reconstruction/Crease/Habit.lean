import YM.SU5.Reconstruction.Crease.House
/-! # obtaining occupancy for continuation into boosted algebra. rank. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub.Club
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Picket CrossedFrame
open scoped BigOperators Topology InnerProductSpace ComplexOrder
variable {H K D:Hilbert}{C:Clasp K H D} {J:Flash H} {M:Net H}{Ω:H}{Γ:Set H.Op}(h:Club C J M Ω Γ)
local notation "P"=>C.plume
local notation "R"=>C.shadow
local notation "Mm"=> M.toStarSubalgebra.toSubalgebra.toSubmodule
-- core useful for pricing.VonNeumannAlgebra needs escort.
include h
lemma home_bank : Dense {x:H|∃ A ∈ M, x=A Ω}:= by
 let Z:Submodule ℂ H:= LinearMap.range ((apply ℂ H.space Ω).toLinearMap.comp (Mm).subtype); have HE(x:H): x∈Z ↔ ∃ A ∈ M,x=A Ω:= ⟨by rintro ⟨y,rfl⟩; exact ⟨y.val,y.property,rfl⟩,by rintro ⟨A,w,rfl⟩; exact ⟨(⟨A,w⟩:Mm),rfl⟩⟩
 rw [show {x:H|_}=↑Z from Set.ext fun y=>(HE y).symm]
 intro x; change x∈ Z.topologicalClosure; refine closure_minimal ?_ Z.isClosed_topologicalClosure (polar_dense C.plume_self (C.plume_inj) x) -- tune
 rintro y ⟨v,rfl⟩; let Q:= Z.topologicalClosure.comap C.plume.toLinearMap
 have Hq : IsClosed (Q:Set H):= Z.isClosed_topologicalClosure.preimage C.plume.continuous
 exact h.economize Q Hq (fun k t=>Z.le_topologicalClosure ((HE (P (label J Ω k))).2 ⟨k,h.pin t,h.pose k t⟩)) Q.zero_mem (fun _ h _ p=> Q.add_mem h p) (fun _ p b=>Q.smul_mem b p) v
-- all reflections see.
lemma away_bank : Dense {x:H|∃ A∈M.commutant, x=A Ω}:= by
 
 have e:DenseRange J.f:=fun x=> subset_closure ⟨J.f x,J.twice x⟩
 refine (e.dense_image J.f.continuous h.home_bank).mono ?_
 rintro _ ⟨k,⟨A,v,rfl⟩,rfl⟩; exact ⟨J.shade A,h.reflect A v,show J.f (A Ω)=_ from (by rw [Flash.shade_at,h.opp])⟩
lemma cheap {A:H.Op}(p:A∈M)(v:A Ω=0): A=0:=by
 ext1 x; apply congrFun (a:=x) (h.away_bank.denseRange_val.equalizer A.continuous continuous_const ?_)
 funext i; obtain ⟨x,a,w,e⟩:=i; dsimp only [Function.comp_apply]; have t:= DFunLike.congr_fun (VonNeumannAlgebra.mem_commutant_iff.mp w A p) Ω; change A x=0; rw [e]; change A (a Ω)=a (A Ω) at t; rw [t,v,map_zero]

end YM.BridgeClub.Club
