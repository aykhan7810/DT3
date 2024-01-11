///////////////////////////////////////////////////////////
//
// audioport_scoreboard
//
// This component instantiates the audioprot_comparator and 
// audioport_predictor and connects them
//
///////////////////////////////////////////////////////////
   
class audioport_scoreboard extends uvm_scoreboard;
   `uvm_component_utils(audioport_scoreboard)

   audioport_predictor m_predictor;
   audioport_comparator m_comparator;   
   uvm_analysis_export #(apb_transaction) apb_analysis_export;
   uvm_analysis_export #(i2s_transaction) i2s_analysis_export;   

   function new(string name, uvm_component parent);
      super.new(name, parent);
      apb_analysis_export = new("apb_analysis_export", this);
      i2s_analysis_export = new("i2s_analysis_export", this);      
   endfunction 
   
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_predictor = audioport_predictor::type_id::create("m_predictor", this);
      m_comparator = audioport_comparator::type_id::create("m_comparator", this);                  
   endfunction
     
   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      apb_analysis_export.connect(m_predictor.apb_analysis_export);
      i2s_analysis_export.connect(m_comparator.i2s_analysis_export);
      m_comparator.predictor_get_port.connect(m_predictor.predictor_get_export);
   endfunction
     
endclass
