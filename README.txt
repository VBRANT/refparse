The repository hosts the RefParse algorithm for parsing bibliographic references.
RefParse is developed by Guido Sautter on behalf of Karlsruhe Institute of 
Technology (KIT) under the ViBRANT project (EU Grant FP7/2007-2013, Virtual
Biodiversity Research and Access Network for Taxonomy).

Copyright (C) 2011-2013 ViBRANT (FP7/2007-2013, GA 261532), by G. Sautter

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program (LICENSE.txt); if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.



SYSTEM REQUIREMENTS

Java Runtime Environment 1.5 or higher, Sun/Oracle JRE recommended



DEPENDENCIES

RefParse builds on other open source projects; the JAR files these projects
build into are included in the "lib" folder for convenience.
In addition, the Ant build script checks if these projects are present in your
workspace, and if so, uses the recent builds found in their "dist" folders.

- idaho-core (http://code.google.com/p/idaho-core/)

- idaho-extensions (http://code.google.com/p/idaho-extensions/)

- refparse (https://git.scratchpads.eu/v/refparse.git)



GETTING STARTED

The Ant script included in this project builds a ZIP file in the "dist"
folder that includes RefParse.jar (the Java parts of RefParse) and a
"RefParseData" folder containing the required configuration files. Simply
un-zip this file where your application is, and your are ready to start.
To use RefParse, you have to instantiate it first, in one of three classes:

- RefParseAutomatic: automatically parses lists of bibliographic references,
                     without user interaction or learning

- RefParseInteractive: automatically parses lists of bibliographic references,
                       then prompty users for corrections of the parse results
                       and learns from this input

- RefParseManual: opens pre-parsed lists of bibliographic references for
                  users to correct manually

Let's assume you are using RefParseAutomatic for the following Java code
example:

===== start of Java code =====

//	instantiate RefParse in its fully automated flavor 
RefParseAutomatic myRefParse = new RefParseAutomatic();

//	tell the RefParse instance where its configuration data is
File myRefParseDataFolder = new File("./RefParseData/");
myRefParse.setDataProvider(new AnalyzerDataProviderFileBased(myRefParseDataFolder));

//	load a list of bibliographic references from an XML file named MyBibRefs.xml,
//	assuming each reference is enclosed by <bibRef> and </bibRef> XML tags, but
//	otherwise contains no markup
File myBibRefsFile = new File("MyBibRefs.xml");
MutableAnnotation myBibRefs = SgmlDocumentReader.readDocument(myBibRefsFile);

//	process a list of bibliographic references
myRefParse.process(myBibRefs, new Properties());

//	output the parse result to System.out
PrintWriter sysOutWriter = new PrintWriter(System.out);
AnnotationUtils.writeXML(myBibRefs, sysOutWriter);

===== end of Java code =====

This little example uses many utility classes from the idaho-core and
idaho-extensions projects, namely all the IO facilities and the data 
representation as a MutableAnnotation. SgmlDocumentReader can also read
from InputStreams and Writers, so you can easily adjust above code for
other scenarios.