/* RefParse, the algorithm for parsing lists of bibliographic references.
 * Copyright (C) 2011-2013 ViBRANT (FP7/2007-2013, GA 261532), by G. Sautter
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */
package de.uka.ipd.idaho.plugins.bibRefs.refParse;

import java.io.File;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.Properties;

import de.uka.ipd.idaho.gamta.MutableAnnotation;
import de.uka.ipd.idaho.gamta.util.Analyzer;
import de.uka.ipd.idaho.gamta.util.AnalyzerDataProviderFileBased;
import de.uka.ipd.idaho.gamta.util.SgmlDocumentReader;

/**
 * Test runner for RefParse.
 * 
 * @author sautter
 */
public class RefParseTest {
	
	/**
	 * @param args
	 */
	public static void main(String[] args) throws Exception {
		Analyzer rp = new RefParseAutomatic();
		rp.setDataProvider(new AnalyzerDataProviderFileBased(new File("E:/GoldenGATEv3/Plugins/AnalyzerData/RefParseData/")));
		
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/zt03911p493.pdf.gs.imf.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/Kucera2013.pdf.names.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/Kucera2013.pdf.names.norm.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/zt00872.pdf.imf.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/zt03131p051.pdf.imf.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/11468_Logunov_2010_Bul_15_85-90.pdf.imf.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/zt00872.pdf.imf.nonCatalog.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/Blepharidatta_revision.pdf.imf.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/29867.pdf.names.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/zt03916p083.pdf.imf.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/Zootaxa/zt03937p049.pdf.imf.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/Zootaxa/zt04072p343.pfd.imf.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/Zootaxa/15611-5134-1-PB.pdf.imf.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/Zootaxa/zt04093p451.pdf.imf.xml")), "utf-8"));
//		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/EJT/EJT-283_Philippe.pdf.xml")), "utf-8"));
		MutableAnnotation doc = SgmlDocumentReader.readDocument(new InputStreamReader(new FileInputStream(new File("E:/Testdaten/PdfExtract/EJT/EJT-261_Reboleira.pdf.xml")), "utf-8"));
		
//		AnnotationFilter.removeDuplicates(doc, EMPHASIS_TYPE);
//		AnnotationFilter.removeAnnotations(doc, TAXONOMIC_NAME_ANNOTATION_TYPE);
//		AnnotationFilter.removeAnnotations(doc, TAXONOMIC_NAME_LABEL_ANNOTATION_TYPE);
//		DocumentStyle docStyle = DocumentStyle.getStyleFor(doc);
//		docStyle.getParameters().setProperty((TAXONOMIC_NAME_ANNOTATION_TYPE + ".binomialsAreBold"), "false");
//		docStyle.getParameters().setProperty((TAXONOMIC_NAME_ANNOTATION_TYPE + ".binomialsAreItalics"), "true");
		rp.process(doc, new Properties());
	}
}